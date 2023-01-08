package typer

import core._
import ast._
import ast.{TypedExprs => tpd}
import Symbols._
import evaluator.{EvalContext, Evaluator, Reducer}
import utils.trace
import core.messages.Errors._
import core.messages.Message.HoleInfo

class Typer extends ConstraintSolving:
  import Typer._
  import DataInfo._
  import Context._

  def defaultError[T](msg: String, srcPos: SrcPos): TyperResult[T] =
    Left(OtherTypeError(msg).setPos(srcPos))

  def isUniverse(e: tpd.Expr)(using Context): TyperResult[Unit] = normalise(e) match
    case _: tpd.Type => Right(())
    case tpd.Wildcard() => Right(())
    case _ => defaultError(s"not supported: isType($e)", null)

  def normalise(e: tpd.Expr)(using Context): tpd.Expr =
    // Evaluator.normalise(e)(using ctx.toEvalContext)
    Reducer.reduce(e)

  def constraint(using Context): EqConstraint = ctx.constraint
  def constraint_=(c: EqConstraint)(using Context): Unit = ctx.constraint = c

  def trackingUVar[T](srcPos: SrcPos)(op: => TyperResult[T])(using Context): TyperResult[T] =
    ctx.enterUVarScope
    val result = op
    val newScope = ctx.uvarScope
    ctx.rollbackUVarScope
    result.flatMap { res =>
      newScope.checkUninstantiated match
        case Nil => Right(res)
        case xs => Left(UnsolvedUVar(srcPos, xs))
    }

  def typedDataDef(ddef: DataDef)(using Context): TyperResult[TypeConInfo] =
    def checkTypeConSig(sig: tpd.Expr): TyperResult[Unit] = sig match
      case tpd.Type(l) => Right(())
      case tpd.PiType(_, _, resTyp) => checkTypeConSig(resTyp)
      case tp => defaultError(s"type constructor must return a type, but found $tp", tp.srcPos)

    def typedDataCon(tyconSym: TypeConSymbol, tycon: TypeConInfo, cdef: ConsDef)(using Context): TyperResult[TypeConInfo => DataConInfo] =
      def checkDataConSig(sig: tpd.Expr): TyperResult[Unit] = sig match
        case tpd.AppliedTypeCon(sym, _) if sym eq tyconSym => Right(())
        case tpd.PiType(_, _, resTyp) => checkDataConSig(resTyp)
        case tp => defaultError(s"data constructor must return ${tycon.name}, but found ${tp.show}", tp.srcPos)
      typed(cdef.sig) flatMap { dataconSig =>
        checkDataConSig(dataconSig) map { _ =>
          (tycon: TypeConInfo) =>
            val sym = DataConSymbol()
            val info = DataConInfo(cdef.name, sym, tycon, dataconSig)
            sym.withInfo(info)
            info
        }
      }

    def typedDataCons(tyconSym: TypeConSymbol, tycon: TypeConInfo, cdefs: List[ConsDef])(using Context): TyperResult[List[TypeConInfo => DataConInfo]] =
      def recur(cds: List[ConsDef], acc: List[TypeConInfo => DataConInfo]): TyperResult[List[TypeConInfo => DataConInfo]] =
        cds match
          case Nil => Right(acc.reverse)
          case cdef :: ds => typedDataCon(tyconSym, tycon, cdef) match
            case Left(err) => Left(err)
            case Right(dinfo) =>
              recur(ds, dinfo :: acc)
      recur(cdefs, Nil)

    typed(ddef.sig) flatMap { tyconSig =>
      checkTypeConSig(tyconSig) flatMap { _ =>
        // type data constructors
        val tyconSym = TypeConSymbol()
        val dummy = TypeConInfo(ddef.name, tyconSym, tyconSig, _ => Nil)
        tyconSym.withInfo(dummy)
        ctx.withDataInfo(dummy) {
          typedDataCons(tyconSym, dummy, ddef.constructors)
        } map { datacons =>
          val res = TypeConInfo(ddef.name, tyconSym, tyconSig, tycon => datacons.map(_(tycon)))
          tyconSym.withInfo(res)
          res
        }
      }
    }

  // def typedDataDef(dataDef: DataDef)(using Context): TyperResult[TypeConInfo] =
  //   def checkTypeConSig(sig: tpd.Expr): TyperResult[Unit] = sig match
  //     case tpd.Type(l) => Right(())
  //     case tpd.PiType(argName, argTyp, resTyp) => checkTypeConSig(resTyp)
  //     case _ => Left(s"invalid datadef signature: ${dataDef.sig}")

  //   def checkDataConSig(sig: tpd.Expr): TyperResult[Unit] = sig match
  //     case tpd.AppliedDataCon(symbol, _) if symbol.name == dataDef.name => Right(())
  //     case tpd.PiType(_, _, resTyp) => checkDataConSig(resTyp)
  //     case _ => Left(s"invalid data constructor signature: $sig")

  //   def typedDataCon(consDef: ConsDef): TyperResult[TypeConInfo => DataConInfo] =
  //     val dummy = TypeConInfo(dataDef.name, ???, _ => Nil)
  //     ctx.withDataInfo(dummy) {
  //       checkDataConSig(consDef.sig).flatMap { _ =>
  //         typed(consDef.sig).map(_ => (info: TypeConInfo) => DataConInfo(consDef.name, info, ???))
  //       }
  //     }

  //   checkTypeConSig(dataDef.sig).flatMap { _ =>
  //     typed(dataDef.sig).flatMap { _ =>
  //       val dataconsM: List[TyperResult[TypeConInfo => DataConInfo]] = dataDef.constructors.map(typedDataCon(_))
  //       collectAll(dataconsM) map { datacons =>
  //         TypeConInfo(dataDef.name, ???, (info: TypeConInfo) => datacons.map(f => f(info)))
  //       }
  //     }
  //   }

  def typedDefDef(ddef: DefDef)(using Context): TyperResult[ValInfo] =
    ctx.lookupValDef(ddef.name) match
      case Some(_) => defaultError(s"already defined: ${ddef.name}", ddef.srcPos)
      case None =>
        typed(ddef.typ) flatMap { sig =>
          ddef.body match
            case None =>
              val sym = ValDefSymbol(ddef.name)
              val res = ValInfo(sym, sig, None)
              sym.overwriteValInfo(res)
              Right(res)
            case Some(body) =>
              val dummySym = ParamSymbol(ddef.name, sig)
              ctx.withBinding(dummySym) {
                typed(body, sig) map { body =>
                  val sym = ValDefSymbol(ddef.name)
                  val body1 = abstractSymbol(dummySym, tpd.ValRef(sym), body)
                  val res = ValInfo(sym, sig, Some(body1))
                  sym.overwriteValInfo(res)
                  res
                }
              }
        }

  def typeMismatch(e: tpd.Expr, pt: tpd.Expr, tp1: tpd.Expr, tp2: tpd.Expr): TyperResult[Unit] =
    Left(TypeMismatch(e, pt, tp1, tp2))

  def compareTypes(e: tpd.Expr, pt: tpd.Expr)(using Context): TyperResult[Unit] =
    def recur(tp1: tpd.Expr, tp2: tpd.Expr): TyperResult[Unit] = trace(s"compareTypes $tp1 >:< $tp2") {
      def issueError = typeMismatch(e, pt, tp1, tp2)
      (tp1, tp2) match
        case (tp1, tp2: tpd.UVarRef) =>
          if tp2.info.instantiated then recur(tp1, tp2.info.instance)
          else if tp1 eq tp2 then Right(())
          else
            tp2.info.instantiate(tp1)
            Right(())
        case (tp1: tpd.UVarRef, tp2) => recur(tp2, tp1)
        case (tpd.AppliedTypeCon(tycon1, args1), tpd.AppliedTypeCon(tycon2, args2)) =>
          if tycon1 eq tycon2 then collectAll(args1 zip args2 map { (a1, a2) => recur(a1, a2) }).map(_ => ())
          else issueError
        case (tpd.PiElim(fun1, arg1), tpd.PiElim(fun2, arg2)) =>
          recur(fun1, fun2) flatMap { _ => recur(arg1, arg2) }
        case (tp1 @ tpd.PiType(argName1, argTyp1, resTyp1), tp2 @ tpd.PiType(argName2, argTyp2, resTyp2)) =>
          recur(argTyp1, argTyp2) flatMap { _ =>
            val sym = ParamSymbol(argName2, argTyp2)
            val resType1 = substBinder(tp1, tpd.ValRef(sym), resTyp1)
            val resType2 = substBinder(tp2, tpd.ValRef(sym), resTyp2)
            recur(resType1, resType2)
          }
        case (tp1 @ tpd.PiIntro(argName1, argTyp1), tp2 @ tpd.PiIntro(argName2, argTyp2)) =>
          recur(argTyp1, argTyp2) flatMap { _ =>
            val sym = ParamSymbol(argName2, argTyp2)
            val body1 = substBinder(tp1, tpd.ValRef(sym), tp1.body)
            val body2 = substBinder(tp2, tpd.ValRef(sym), tp2.body)
            recur(body1, body2)
          }
        case (tp1, tp2) => if tp1 == tp2 then Right(()) else issueError
    }
    recur(normalise(e.tpe), pt)

  def isMatchingTypes(e: tpd.Expr, pt: tpd.Expr | Null)(using Context): TyperResult[Unit] = trace(s"isMatchingTypes(${e.tpe}, $pt)") {
    pt match {
      case null => Right(())
      case pt: tpd.Expr =>
        compareTypes(e, normalise(pt))
    }
  }

  def typed(e: Expr, pt: tpd.Expr | Null = null)(using Context): TyperResult[tpd.Expr] =
    val showPt = if pt eq null then "<null>" else pt.toString
    // println(s"typing $e, pt = $showPt")
    trace(s"typing $e, pt = $showPt") {
      typed1(e, pt).map(_.setPos(e.srcPos)) flatMap { e1 =>
        isMatchingTypes(e1, pt).map(_ => e1)
      }
    }

  def adaptImplicit(expr: tpd.Expr, pt: tpd.Expr | Null)(using Context): TyperResult[tpd.Expr] =
    def go(e: tpd.Expr, pt: tpd.Expr): TyperResult[tpd.Expr] =
      normalise(e.tpe) match
        case tp1 @ tpd.PiType(arg1, typ1, resTyp1) if tp1.isImplicitFunction =>
          val tp2 = normalise(pt)
          tp2 match
            case tp2 @ tpd.PiType(_, _, _) if tp2.isImplicitFunction => Right(e)
            case _ =>
              val arg0 = tpd.UVarRef(UVarInfo(arg1, typ1, CreationSite(expr.srcPos, "implicit argument")))
              typedApplyFunction(e, arg0, imp = true) flatMap { fun0 => go(fun0, tp2) }
        case _ => Right(e)
    pt match
      case null => Right(expr)
      case pt: tpd.Expr => go(expr, pt)

  def lookupConstructor(name: String, pt: tpd.Expr | Null)(using Context): Option[TypeConInfo | DataConInfo] =
    def expectedTypeCon: Option[String] =
      if pt eq null then None else
        normalise(pt) match
          case tpd.AppliedTypeCon(sym, _) => Some(sym.name)
          case _ => None
    def lookupTypeCon: Option[TypeConInfo | DataConInfo] = ctx.lookupTypeConInfo(name)
    def lookupDataCon: Option[TypeConInfo | DataConInfo] = ctx.lookupDataConInfo(name, expectedTypeCon)
    lookupTypeCon orElse lookupDataCon

  def adaptConstructor(srcPos: SrcPos, name: String, pt: tpd.Expr | Null, errMsg: TypeError)(using Context): TyperResult[tpd.Expr] =
    def isAdaptableSig(sig: tpd.Expr): Boolean =
      @annotation.tailrec def recur(sig: tpd.Expr): Boolean = sig match
        case sig @ tpd.PiType(_, _, resTyp) => sig.isImplicitFunction && recur(resTyp)
        case _ => true
      recur(sig)
    def adaptSig(con: TypeConSymbol | DataConSymbol, sig: tpd.Expr): TyperResult[tpd.Expr] =
      def recur(e: tpd.Expr): TyperResult[tpd.Expr] = e.tpe match
        case fun @ tpd.PiType(argName, argTyp, resTyp) =>
          assert(fun.isImplicitFunction)
          val arg0 = tpd.UVarRef(UVarInfo(ctx.freshen(argName), argTyp, CreationSite(srcPos, "implicit argument")))
          typedApplyFunction(e, arg0, imp = true) flatMap { fun0 =>
            recur(fun0)
          }
        case _ => Right(e)
      val dummy: tpd.Expr = tpd.Wildcard().withType(sig).setPos(srcPos)
      recur(dummy) map { adapted =>
        val args = retriveAppliedArguments(adapted)
        (con, normalise(adapted.tpe)) match
          case (sym: TypeConSymbol, tpe @ tpd.Type(_)) => tpd.AppliedTypeCon(sym, args).withType(tpe)
          case (sym: DataConSymbol, tpe @ tpd.AppliedTypeCon(_, _)) =>
            tpd.AppliedDataCon(sym, args).withType(tpe)
          case e => assert(false, e)
      }

    lookupConstructor(name, pt) match
      case None => Left(errMsg)
      case Some(info: TypeConInfo) =>
        if isAdaptableSig(info.sig) then adaptSig(info.symbol, info.sig)
        else Left(errMsg)
      case Some(info: DataConInfo) =>
        if isAdaptableSig(info.sig) then adaptSig(info.symbol, info.sig)
        else Left(errMsg)

  def typed1(e: Expr, pt: tpd.Expr | Null = null)(using Context): TyperResult[tpd.Expr] = e match
    case Var(name) => ctx.lookupVal(name) match {
      case Some(sym) =>
        val res = tpd.ValRef(sym).setPos(e.srcPos)
        adaptImplicit(res, pt).map(res1 =>
          // println(s"adapting $res (${res.tpe}), pt = $pt ===> $res1")
          res1
        )
      case None =>
        adaptConstructor(e.srcPos, name, pt, errMsg = OtherTypeError(s"unknown variable $name").setPos(e.srcPos))
        // Left(s"unknown variable $name")
    }
    case Apply(expr, args, imp) => typedApply(expr, args, pt, e.srcPos, imp)
    case ApplyTypeCon(name, iargs, args) =>
      ctx.lookupTypeConInfo(name) match
        case None => defaultError(s"unknown type constructor $name", e.srcPos)
        case Some(tycon) => typedApplyTypeCon(tycon, iargs, args, e.srcPos)
    case ApplyDataCon(name, iargs, args) =>
      def getExpectedTypeCon: Option[String] =
        pt match
          case tpd.AppliedTypeCon(sym, _) => Some(sym.name)
          case _ => None

      ctx.lookupDataConInfo(name, getExpectedTypeCon) match
        case None => defaultError(s"unknown data constructor $name", e.srcPos)
        case Some(con) => typedApplyDataCon(con, iargs, args, e.srcPos)
    case Pi(arg, typ, resTyp, imp) => typedPi(arg, typ, resTyp, imp)
    case PiIntro(argName, body) => typedPiIntro(argName, body, pt, e.srcPos)
    case e @ Match(scrutinee, cases) => typedMatch(e, pt)
    case e @ Type(l) => typedType(e, pt)
    case Level() => Right(tpd.Level())
    case LZero() => Right(tpd.LZero())
    case LSucc(l) =>
      typed(l, tpd.Level()) map { l => tpd.LSucc(l) }
    case LLub(e1, e2) =>
      typed(e1, tpd.Level()) flatMap { l1 =>
        typed(e2, tpd.Level()) map { l2 =>
          tpd.LLub(l1, l2)
        }
      }
    case Undefined() =>
      if pt == null then
        defaultError(s"cannot type ??? w/o an expected type", e.srcPos)
      else
        // println(s"Goal: ${normalise(pt).show}")
        // // println(s"normalising ${pt.show} --> ${normalise(pt).show}")
        // // println(s"constraint = ${ctx.constraint.show}")
        // println(s"=====================")
        // println(ctx.description(e => normalise(e).show))
        // println(s"---------------------")
        // println(ctx.constraint.show ++ "\n")
        ctx.report(HoleInfo(ctx, normalise(pt)))
        Right(tpd.Wildcard().withType(pt))
    case e: Block => typedBlock(e, pt)
    case OmittedType =>
      val tp0 = tpd.UVarRef(UVarInfo(ctx.freshen("resultType"), tpd.Type(tpd.LZero()), CreationSite(e.srcPos, "result type")))
      Right(tp0)
    case _ => assert(false, s"not supported: typed($e)")

  def typedType(e: Type, pt: tpd.Expr | Null = null)(using Context): TyperResult[tpd.Expr] =
    typed(e.level, pt = tpd.Level()) map { l => tpd.Type(l) }

  private def liftParamRefInType(from: tpd.PiIntroParamRef, to: tpd.PiTypeParamRef, tp: tpd.Expr): tpd.Expr =
    val treeMap = new tpd.ExprMap:
      // override def isDebugging: Boolean = true
      override def mapPiIntroParamRef(e: tpd.PiIntroParamRef): ast.TypedExprs.Expr =
        if e eq from then to else super.mapPiIntroParamRef(e)
    treeMap(tp)

  def typedPi(argName: String, argTyp: Expr, resTyp: Expr, isImp: Boolean)(using Context): TyperResult[tpd.Expr] =
    typed(argTyp) flatMap { argTyp1 =>
      normalise(argTyp1.tpe) match
        case tpd.Type(l1) =>
          val sym = ParamSymbol(argName, argTyp1)
          ctx.withBinding(sym) {
            typed(resTyp)
          } flatMap { resTyp1 =>
            resTyp1.tpe match
              case tpd.Type(l2) =>
                val l = tpd.LLub(l1, l2)
                val pref = tpd.PiTypeParamRef()
                val resTyp2 = abstractSymbol(sym, pref, resTyp1)
                val binder = tpd.PiType(argName, argTyp1, resTyp2).withType(tpd.Type(l))
                pref.overwriteBinder(binder)
                Right(if isImp then binder.asImplicit else binder)
              case _ => defaultError(s"return type $resTyp1 is not a type", resTyp.srcPos)
          }
        case _ => defaultError(s"cannot abstract over ${argTyp1.show}, which is not a type (its type is ${argTyp1.tpe.show})", resTyp.srcPos)
    }

  def typedPiIntro(argName: String, body: Expr, pt: tpd.Expr, srcPos: SrcPos)(using Context): TyperResult[tpd.Expr] =
    pt match
      case pt @ tpd.PiType(eargName, eargTyp, eresTyp) =>
        isUniverse(eargTyp.tpe) flatMap { _ =>
          val binder = tpd.PiIntro(eargName, eargTyp)
          val sym = ParamSymbol(eargName, eargTyp)
          ctx.withBinding(sym)(typed(substBinder(argName, Var(eargName), body), substBinder(pt, tpd.ValRef(sym), eresTyp))) map { body =>
            val pref = tpd.PiIntroParamRef().overwriteBinder(binder)
            val body1 = abstractSymbol(sym, pref, body)

            val tpref = tpd.PiTypeParamRef()
            val tpe = tpd.PiType(eargName, eargTyp, liftParamRefInType(pref, tpref, body1.tpe)).withType()
            tpref.overwriteBinder(tpe)
            binder.withBody(body1).withType(tpe)
          }
        }
      case _ => defaultError(s"cannot type function with expected type $pt", srcPos)

  def typedMatch(e: Match, pt: tpd.Expr | Null)(using Context): TyperResult[tpd.Expr] =
    typed(e.scrutinee) flatMap { scrutinee =>
      normalise(scrutinee.tpe) match
        case scrutTyp @ tpd.AppliedTypeCon(tycon, args) =>
          def typedPattern(pat: ApplyDataCon): TyperResult[(tpd.AppliedDataCon, List[ParamSymbol])] =
            ctx.lookupDataConInfo(pat.name, Some(tycon.name)) match
              case Some(dcon) =>
                @annotation.tailrec def recur(iargs: List[Expr], args: List[Expr], accTyp: tpd.Expr, acc: List[ParamSymbol]): TyperResult[(tpd.AppliedDataCon, List[ParamSymbol])] =
                  iargs match
                    case Var(name) :: iargs =>
                      accTyp match
                        case binder @ tpd.PiType(argName, argTyp, resTyp) =>
                          if binder.isImplicitFunction then
                            val sym = ParamSymbol(name, argTyp)
                            val nextTyp = substBinder(binder, tpd.ValRef(sym), resTyp)
                            recur(iargs, args, nextTyp, sym :: acc)
                          else defaultError(s"too many implicits arguments in pattern $pat", pat.srcPos)
                        case _ =>
                          defaultError(s"too many arguments in pattern $pat", pat.srcPos)
                    case e :: iargs => defaultError(s"nested pattern is not supported", e.srcPos)
                    case Nil =>
                      args match
                        case Nil => accTyp match
                          case tpe: tpd.AppliedTypeCon =>
                            val args = acc.reverse.map(tpd.ValRef(_))
                            Right((tpd.AppliedDataCon(dcon.symbol, args).withType(tpe), acc.reverse))
                          case binder @ tpd.PiType(argName, argTyp, resTyp) if binder.isImplicitFunction =>
                            val sym = ParamSymbol(ctx.freshen(argName), argTyp)
                            val nextTyp = substBinder(binder, tpd.ValRef(sym), resTyp)
                            recur(Nil, Nil, nextTyp, sym :: acc)
                          case _ => defaultError(s"incorrect number of arguments in pattern $pat", pat.srcPos)
                        case allArgs @ (Var(name) :: args) => accTyp match
                          case binder @ tpd.PiType(argName, argTyp, resTyp) =>
                            if binder.isImplicitFunction then
                              val sym = ParamSymbol(ctx.freshen(argName), argTyp)
                              val nextTyp = substBinder(binder, tpd.ValRef(sym), resTyp)
                              recur(Nil, allArgs, nextTyp, sym :: acc)
                            else
                              val sym = ParamSymbol(name, argTyp)
                              val nextTyp = substBinder(binder, tpd.ValRef(sym), resTyp)
                              recur(Nil, args, nextTyp, sym :: acc)
                          case other => defaultError(s"incorrect number of arguments in pattern $pat", pat.srcPos)
                        case exp :: args => defaultError(s"nested pattern is not supported", exp.srcPos)
                recur(pat.iargs, pat.args, dcon.sig, Nil)
              case None => defaultError(s"unknown data constructor ${pat.name}", pat.srcPos)
          def typedCase(cdef: CaseDef)(using Context): TyperResult[tpd.CaseDef] = trackingUVar(cdef.srcPos) {
            typedPattern(cdef.pat) flatMap { case (pat, paramSyms) =>
              def updateConstraint: SolverResult[Unit] =
                addEquality(pat, scrutinee) flatMap { _ =>
                  addEquality(pat.tpe, scrutTyp)
                }
              val isImpossiblePattern: Boolean = updateConstraint.isLeft
              // updateConstraint match
              //   case Left(err) => println(s"impossible pattern: $err")
              //   case _ =>
              if isImpossiblePattern then
                val prefs = paramSyms.zipWithIndex.map((_, i) => tpd.PatternBoundParamRef(i))
                val mapping: Map[ValSymbol, tpd.PatternBoundParamRef] = Map.from(paramSyms zip prefs)
                val substitutor = new tpd.ExprMap:
                  override def mapValRef(e: tpd.ValRef): tpd.Expr =
                    mapping.get(e.sym) match
                      case None => super.mapValRef(e)
                      case Some(pref) => pref
                val body1 = tpd.Wildcard().withType(pt)
                val argTyps = paramSyms.map(sym => substitutor(sym.info))
                val resPat = tpd.Pattern(pat.datacon, paramSyms.map(_.name), argTyps)
                val res = tpd.CaseDef(resPat, body1)
                prefs.foreach(_.overwriteBinder(res))
                if cdef.body.isDefined then
                  defaultError(s"impossible case should have `()` as the body", cdef.body.get.srcPos)
                else Right(res)
              else
                cdef.body match
                  case None => defaultError(s"this is not an impossible pattern", pat.srcPos)
                  case Some(body) =>
                    ctx.withBindings(paramSyms) {
                      typed(body, pt = pt) map { body =>
                        val prefs = paramSyms.zipWithIndex.map((_, i) => tpd.PatternBoundParamRef(i))
                        val mapping: Map[ValSymbol, tpd.PatternBoundParamRef] = Map.from(paramSyms zip prefs)
                        val substitutor = new tpd.ExprMap:
                          override def mapValRef(e: tpd.ValRef): tpd.Expr =
                            mapping.get(e.sym) match
                              case None => super.mapValRef(e)
                              case Some(pref) => pref
                        val body1 = substitutor(body)
                        val argTyps = paramSyms.map(sym => substitutor(sym.info))
                        val resPat = tpd.Pattern(pat.datacon, paramSyms.map(_.name), argTyps)
                        val res = tpd.CaseDef(resPat, body1)
                        prefs.foreach(_.overwriteBinder(res))
                        res
                      }
                    }
            }
          }
          collectAll(e.cases.map(x => typedCase(x)(using ctx.fresh))).flatMap { cases =>
            val res = tpd.Match(scrutinee)
            cases.foreach(_.overwritePatMat(res))
            val datacons = cases.map(_.pat.datacon)
            val allDataCons = tycon.info.constructors.map(_.symbol)
            val missing = allDataCons.filter(sym =>
              !datacons.exists(x => x.name == sym.name)
            )
            if missing.isEmpty then
              res.setCases(cases)
              Right(res.withType(pt))
            else
              defaultError(s"missing cases: $missing", e.scrutinee.srcPos)
          }
        case other => defaultError(s"cannot pattern match $scrutinee of type $other", e.scrutinee.srcPos)
    }

  def retriveAppliedArguments(expr: tpd.Expr): List[tpd.Expr] =
    @annotation.tailrec def recur(e: tpd.Expr, acc: List[tpd.Expr]): List[tpd.Expr] = e match
      case tpd.PiElim(app, arg) => recur(app, arg :: acc)
      case _ => acc
    recur(expr, Nil)

  def typedApplyTypeCon(info: TypeConInfo, iargs: List[Expr], args: List[Expr], srcPos: SrcPos)(using Context): TyperResult[tpd.Expr] =
    val dummy: tpd.Expr = tpd.Wildcard().withType(info.sig).setPos(srcPos)
    val typedImpArgs = typedApplyFunctionParams(dummy, iargs, imp = true)
    val typedAllArgs = typedImpArgs flatMap { fun0 => typedApplyFunctionParams(fun0, args, imp = false) }
    typedAllArgs flatMap { res =>
      normalise(res.tpe) match
        case resTyp @ tpd.Type(_) =>
          val args = retriveAppliedArguments(res)
          Right(tpd.AppliedTypeCon(info.symbol, args).withType(resTyp))
        case resTyp => Left(ConstructorNotFullyApplied(srcPos, info, resTyp))
    }

  def typedApplyDataCon(info: DataConInfo, iargs: List[Expr], args: List[Expr], srcPos: SrcPos)(using Context): TyperResult[tpd.Expr] =
    val dummy: tpd.Expr = tpd.Wildcard().withType(info.sig).setPos(srcPos)
    val typedImpArgs = typedApplyFunctionParams(dummy, iargs, imp = true)
    val typedAllArgs = typedImpArgs flatMap { fun0 => typedApplyFunctionParams(fun0, args, imp = false) }
    typedApplyFunctionParams(dummy, args) flatMap { res =>
      normalise(res.tpe) match
        case resTyp @ tpd.AppliedTypeCon(_, _) =>
          val args = retriveAppliedArguments(res)
          Right(tpd.AppliedDataCon(info.symbol, args).withType(resTyp))
        case resTyp => Left(ConstructorNotFullyApplied(srcPos, info, resTyp))
    }

  def typedApplyFunction(fun: tpd.Expr, arg: tpd.Expr | Expr, imp: Boolean = false)(using Context): TyperResult[tpd.Expr] =
    normalise(fun.tpe) match
      case funType @ tpd.PiType(argName, typ, resTyp) =>
        if !funType.isImplicitFunction && imp then
          defaultError(s"function of ${funType.show} does not take implicit arguments", fun.srcPos)
        else if funType.isImplicitFunction && !imp then
          val info = UVarInfo(ctx.freshen(argName), typ, CreationSite(fun.srcPos, "implicit argument"))
          val arg0 = tpd.UVarRef(info)
          typedApplyFunction(fun, arg0, imp = true) flatMap { fun0 =>
            // println(s"completing implicit: ${fun0.show}")
            typedApplyFunction(fun0, arg)
          }
        else
          def typedArg: TyperResult[tpd.Expr] = arg match
            case arg: tpd.Expr => Right(arg)
            case arg: Expr => typed(arg, typ)
          typedArg map { arg =>
            val tpe = substBinder(funType, arg, resTyp)
            tpd.PiElim(fun, arg).withType(tpe).setPos(fun.srcPos to arg.srcPos)
          }
      case _ => defaultError(s"cannot apply value $fun of type ${fun.tpe}", fun.srcPos)

  def typedApplyFunctionParams(fun: tpd.Expr, arg: List[Expr], imp: Boolean = false)(using Context): TyperResult[tpd.Expr] =
    def recur(xs: List[Expr], acc: TyperResult[tpd.Expr]): TyperResult[tpd.Expr] = xs match
      case Nil => acc
      case x :: xs => recur(xs, acc.flatMap(typedApplyFunction(_, x, imp)))
    recur(arg, Right(fun))

  def typedApply(fun: Expr, args: List[Expr], pt: tpd.Expr | Null, srcPos: SrcPos, isImp: Boolean = false)(using Context): TyperResult[tpd.Expr] =
    def expectedTypeCon: Option[String] =
      if pt eq null then None else
        normalise(pt) match
          case tpd.AppliedTypeCon(tycon, _) => Some(tycon.name)
          case _ => None
    def lookupTypeCon(name: String): Option[TypeConInfo] = ctx.lookupTypeConInfo(name)
    def lookupDataCon(name: String): Option[DataConInfo] = ctx.lookupDataConInfo(name, expectedTypeCon)
    def tryApplyCon: Option[TyperResult[tpd.Expr]] =
      val getArgs = fun match
        case Apply(Var(conName), args1, isImp1) if !isImp && isImp1 => Some((conName, args1, args))
        case Var(conName) => Some((conName, Nil, args))
        case _ => None
      getArgs flatMap { case (conName, iargs, args) =>
        lookupTypeCon(conName) orElse lookupDataCon(conName) map {
          case info: TypeConInfo =>
            typedApplyTypeCon(info, iargs, args, srcPos)
          case info: DataConInfo =>
            typedApplyDataCon(info, iargs, args, srcPos)
        }
      }
    def typeAsFunction =
      typed(fun) flatMap { fun =>
        typedApplyFunctionParams(fun, args, isImp)
      }
    tryApplyCon getOrElse typeAsFunction

  def typedBlock(e: Block, pt: tpd.Expr | Null = null)(using Context): TyperResult[tpd.Expr] =
    def recur(ds: List[DefDef], acc: List[ValDefSymbol], e: Expr)(using Context): TyperResult[tpd.Expr] =
      ds match
        case Nil =>
          def build(e: tpd.Expr, acc: List[ValDefSymbol]): tpd.Expr =
            acc match
              case Nil => e
              case sym :: acc =>
                val pref = tpd.PiIntroParamRef()
                val tpref = tpd.PiTypeParamRef()
                val body = abstractSymbol(sym, pref, e)
                val binder = tpd.PiIntro(sym.name, body)
                val tpe = tpd.PiType(sym.name, sym.info, liftParamRefInType(pref, tpref, body)).withType()
                binder.withType(tpe)
                pref.overwriteBinder(binder)
                tpref.overwriteBinder(tpe)
                val arg = sym.dealias.expr
                val app = tpd.PiElim(binder, arg.get).withType(substBinder(tpe, arg.get, tpe.resTyp)).setPos(e.srcPos)
                build(app, acc)
          typed(e, pt)
        case d :: ds =>
          d.body match
            case None => defaultError(s"cannot assume definitions in a local block", d.srcPos)
            case Some(_) =>
              typedDefDef(d) flatMap { dinfo =>
                ctx.withValInfo(dinfo, local = true) { recur(ds, dinfo.sym :: acc, e) }
              }
    recur(e.ddefs, Nil, e.expr)

  def typedDefinition(d: Definition)(using Context): TyperResult[Unit] = trackingUVar(d.srcPos) {
    d match
      case ddef: DataDef => typedDataDef(ddef) map { info => ctx.addDataInfo(info) }
      case ddef: DefDef => typedDefDef(ddef) map { info => ctx.addValInfo(info) }
      case p: Commands.Normalise => typed(p.expr) map { te =>
        println(Reducer.reduce(te).show)
      }
      case _ => assert(false, s"unsupported: $d")
  }

  def typedProgram(defs: List[Definition])(using Context): TyperResult[Unit] =
    def recur(ds: List[Definition]): TyperResult[Unit] =
      ds match
        case Nil => Right(())
        case d :: ds => typedDefinition(d) flatMap { _ => recur(ds) }
    recur(defs)

object Typer:
  type TyperResult[+X] = Either[TypeError, X]

  def substBinder[T <: tpd.PiType | tpd.PiIntro](binder: T, to: tpd.Expr, expr: tpd.Expr): tpd.Expr =
    val exprMap = new tpd.ExprMap:
      override def mapPiTypeParamRef(e: tpd.PiTypeParamRef): tpd.Expr =
        // println(s"!!! mapPiTypeParamRef ($binder --> $to) $e")
        if e.binder.exprId == binder.exprId then to else super.mapPiTypeParamRef(e)

      override def mapPiIntroParamRef(e: tpd.PiIntroParamRef): tpd.Expr =
        // println(s"!!! mapPiIntroParamRef ($binder --> $to) $e")
        // println(s"... e.binder: ${e.binder}")
        // println(s"... binder: ${binder}")
        if e.binder.exprId == binder.exprId then to else super.mapPiIntroParamRef(e)
    exprMap(expr)

  def substBinder(name: String, to: Expr, ddef: DefDef): DefDef =
    val typ1 = substBinder(name, to, ddef.typ)
    val body1 = if name == ddef.name then ddef.body else ddef.body.map(body => substBinder(name, to, body))
    DefDef(ddef.name, typ1, body1)

  def substBinder(name: String, to: Expr, expr: Expr): Expr =
    def k(expr: Expr): Expr = substBinder(name, to, expr)
    val res =
      expr match
        case Var(name1) => if name1 == name then to else Var(name1)
        case Pi(arg, typ, resTyp, imp) => if arg == name then expr else Pi(arg, k(typ), k(resTyp), imp)
        case PiIntro(arg, body) => if arg == name then expr else PiIntro(arg, k(body))
        case Apply(func, args, imp) => Apply(k(func), args.map(k), imp)
        case ApplyTypeCon(name, iargs, args) => ApplyTypeCon(name, iargs.map(k), args.map(k))
        case ApplyDataCon(name, iargs, args) => ApplyDataCon(name, iargs.map(k), args.map(k))
        case Match(scrutinee, cases) => Match(k(scrutinee), cases.map { case cdef @ CaseDef(pat, body) => CaseDef(k(pat).asInstanceOf, body.map(k)).setPos(cdef.srcPos) })
        case Type(level) => Type(k(level))
        case Level() => expr
        case LZero() => expr
        case LSucc(pred) => LSucc(k(pred))
        case LLub(l1, l2) => LLub(k(l1), k(l2))
        case Undefined() => Undefined()
        case Block(ddefs, e) =>
          def recur(ddefs: List[DefDef], acc: List[DefDef], e: Expr): Block =
            ddefs match
              case Nil => Block(acc.reverse, k(e))
              case ddef :: ds =>
                val ddef1 = substBinder(name, to, ddef)
                if ddef1.name == name then Block(acc.reverse ++ (ddef1 :: ds), e)
                else recur(ds, ddef1 :: acc, e)
          recur(ddefs, Nil, e)
        case Wildcard => Wildcard
        case OmittedType => OmittedType
    res.setPos(expr.srcPos)

  def abstractSymbol(sym: ValSymbol, target: tpd.Expr, e: tpd.Expr): tpd.Expr =
    val treeMap = new tpd.ExprMap:
      override def mapValRef(e: tpd.ValRef): tpd.Expr =
        if e.sym eq sym then target else super.mapValRef(e)
      // override def apply(e: tpd.Expr): tpd.Expr =
      //   println(s"abstracting symbol for $e")
      //   super.apply(e)
    treeMap(e)

  def collectAll[E, X](xs: List[Either[E, X]]): Either[E, List[X]] = xs match
    case Nil => Right(Nil)
    case x :: xs => x.flatMap(x => collectAll(xs).map(x :: _))
