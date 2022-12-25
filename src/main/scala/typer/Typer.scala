package  typer

import core._
import ast._
import ast.{TypedExprs => tpd}
import Symbols._
import ast.TypedExprs.PiTypeParamRef
import ast.TypedExprs.PiIntroParamRef

class Typer:
  import Typer._
  import DataInfo._
  import Context._

  def isUniverse(e: tpd.Expr)(using Context): TyperResult[Unit] = e match
    case _: tpd.Type => Right(())
    case tpd.Wildcard() => Right(())
    case _ => Left(s"not supported: isType($e)")

  def typedDataDef(ddef: DataDef)(using Context): TyperResult[TypeConInfo] =
    def checkTypeConSig(sig: tpd.Expr): TyperResult[Unit] = sig match
      case tpd.Type(l) => Right(())
      case tpd.PiType(_, _, resTyp) => checkTypeConSig(resTyp)
      case tp => Left(s"type constructor must return a type, but found $tp")

    def typedDataCon(tyconSym: TypeConSymbol, tycon: TypeConInfo, cdef: ConsDef)(using Context): TyperResult[TypeConInfo => DataConInfo] =
      def checkDataConSig(sig: tpd.Expr): TyperResult[Unit] = sig match
        case tpd.AppliedTypeCon(sym, _) if sym eq tyconSym => Right(())
        case tpd.PiType(_, _, resTyp) => checkDataConSig(resTyp)
        case tp => Left(s"data constructor must return ${tycon.name}, but found $tp")
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

  def compareTypes(tp1: tpd.Expr, tp2: tpd.Expr)(using Context): TyperResult[Unit] =
    (tp1, tp2) match
      case (tp1 @ tpd.PiType(argName1, argTyp1, resTyp1), tp2 @ tpd.PiType(argName2, argTyp2, resTyp2)) =>
        compareTypes(argTyp1, argTyp2) flatMap { _ =>
          val sym = ParamSymbol(argName2, argTyp2)
          val resType1 = substBinder(tp1, tpd.ValRef(sym), resTyp1)
          val resType2 = substBinder(tp2, tpd.ValRef(sym), resTyp2)
          compareTypes(resType1, resType2)
        }
      case (tp1 @ tpd.PiIntro(argName1, argTyp1), tp2 @ tpd.PiIntro(argName2, argTyp2)) =>
        compareTypes(argTyp1, argTyp2) flatMap { _ =>
          val sym = ParamSymbol(argName2, argTyp2)
          val body1 = substBinder(tp1, tpd.ValRef(sym), tp1.body)
          val body2 = substBinder(tp2, tpd.ValRef(sym), tp2.body)
          compareTypes(body1, body2)
        }
      case (tp1, tp2) => if tp1 == tp2 then Right(()) else Left(s"Type mismatch: $tp1 vs $tp2")

  def isMatchingTypes(tp: tpd.Expr, pt: tpd.Expr | Null)(using Context): TyperResult[Unit] =
    // isUniverse(tp) flatMap { _ =>
    //   isUniverse(pt) flatMap { _ =>
        pt match {
          case null => Right(())
          case pt: tpd.Expr => compareTypes(tp, pt)
        }
    //   }
    // }

  def substBinder[T <: tpd.PiType | tpd.PiIntro](binder: T, to: tpd.Expr, expr: tpd.Expr)(using Context): tpd.Expr =
    val exprMap = new tpd.ExprMap:
      override def mapPiTypeParamRef(e: tpd.PiTypeParamRef): tpd.Expr =
        if e.binder eq binder then to else super.mapPiTypeParamRef(e)

      override def mapPiIntroParamRef(e: tpd.PiIntroParamRef): tpd.Expr =
        if e.binder eq binder then to else super.mapPiIntroParamRef(e)
    exprMap(expr)

  def substBinder(name: String, to: Expr, expr: Expr)(using Context): Expr =
    def k(expr: Expr): Expr = substBinder(name, to, expr)
    expr match
      case Var(name1) => if name1 == name then to else Var(name1)
      case Pi(arg, typ, resTyp) => if arg == name then expr else Pi(arg, k(typ), k(resTyp))
      case PiIntro(arg, body) => if arg == name then expr else PiIntro(arg, k(body))
      case Apply(func, args) => Apply(k(func), args.map(k))
      case ApplyTypeCon(name, args) => ApplyTypeCon(name, args.map(k))
      case ApplyDataCon(name, args) => ApplyDataCon(name, args.map(k))
      case Match(scrutinee, cases) => Match(k(scrutinee), cases.map { case CaseDef(pat, body) => CaseDef(k(pat).asInstanceOf, k(body)) })
      case Type(level) => expr
      case Wildcard => Wildcard

  def typed(e: Expr, pt: tpd.Expr | Null = null)(using Context): TyperResult[tpd.Expr] =
    val showPt = if pt eq null then "<null>" else pt.toString
    // println(s"typing $e, pt = $showPt")
    typed1(e, pt) flatMap { e1 =>
      isMatchingTypes(e1.tpe, pt).map(_ => e1)
    }

  def typed1(e: Expr, pt: tpd.Expr | Null = null)(using Context): TyperResult[tpd.Expr] = e match
    case Var(name) => ctx.lookupBindings(name) match {
      case Some(sym) => Right(tpd.ValRef(sym))
      case None => Left(s"unknown variable $name")
    }
    case Apply(expr, args) => typedApply(expr, args)
    case ApplyTypeCon(name, args) =>
      ctx.lookupTypeConInfo(name) match
        case None => Left(s"unknown type constructor $name")
        case Some(tycon) => typedApplyTypeCon(tycon, args)
    case ApplyDataCon(name, args) =>
      def getExpectedTypeCon: Option[String] =
        pt match
          case ApplyTypeCon(name, _) => Some(name)
          case _ => None

      ctx.lookupDataConInfo(name, getExpectedTypeCon) match
        case None => Left(s"unknown data constructor $name")
        case Some(con) => typedApplyDataCon(con, args)
    case Pi(arg, typ, resTyp) => typedPi(arg, typ, resTyp)
    case PiIntro(argName, body) => typedPiIntro(argName, body, pt)
    case Type(l) => Right(tpd.Type(l))
    case _ => Left(s"not supported: typed($e)")

  private def abstractSymbol(sym: ValSymbol, target: tpd.Expr, e: tpd.Expr)(using Context): tpd.Expr =
    val treeMap = new tpd.ExprMap:
      override def mapValRef(e: tpd.ValRef): tpd.Expr =
        if e.sym eq sym then target else super.mapValRef(e)
      // override def apply(e: tpd.Expr): tpd.Expr =
      //   println(s"abstracting symbol for $e")
      //   super.apply(e)
    treeMap(e)

  private def liftParamRefInType(from: tpd.PiIntroParamRef, to: tpd.PiTypeParamRef, tp: tpd.Expr): tpd.Expr =
    val treeMap = new tpd.ExprMap:
      // override def isDebugging: Boolean = true
      override def mapPiIntroParamRef(e: PiIntroParamRef): ast.TypedExprs.Expr =
        if e eq from then to else super.mapPiIntroParamRef(e)
    treeMap(tp)

  def typedPi(argName: String, argTyp: Expr, resTyp: Expr)(using Context): TyperResult[tpd.Expr] =
    typed(argTyp) flatMap { argTyp1 =>
      argTyp1.tpe match
        case tpd.Type(l1) =>
          val sym = ParamSymbol(argName, argTyp1)
          ctx.withBinding(sym) {
            typed(resTyp)
          } flatMap { resTyp1 =>
            resTyp1.tpe match
              case tpd.Type(l2) =>
                val l = l1 lub l2
                val pref = tpd.PiTypeParamRef()
                val resTyp2 = abstractSymbol(sym, pref, resTyp1)
                val binder = tpd.PiType(argName, argTyp1, resTyp2).withType(tpd.Type(l))
                pref.overwriteBinder(binder)
                Right(binder)
              case _ => Left(s"return type $resTyp1 is not a type")
          }
        case _ => Left(s"cannot abstract over $argTyp1")
    }

  def typedPiIntro(argName: String, body: Expr, pt: tpd.Expr)(using Context): TyperResult[tpd.Expr] =
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
      case _ => Left(s"cannot type function with expected type $pt")

  def collectAll[X](xs: List[TyperResult[X]]): TyperResult[List[X]] = xs match
    case Nil => Right(Nil)
    case x :: xs => x.flatMap(x => collectAll(xs).map(x :: _))

  def retriveAppliedArguments(expr: tpd.Expr): List[tpd.Expr] =
    @annotation.tailrec def recur(e: tpd.Expr, acc: List[tpd.Expr]): List[tpd.Expr] = e match
      case tpd.PiElim(app, arg) => recur(app, arg :: acc)
      case _ => acc
    recur(expr, Nil)

  def typedApplyTypeCon(info: TypeConInfo, args: List[Expr])(using Context): TyperResult[tpd.Expr] =
    if args.length == info.paramNum then
      val dummy: tpd.Expr = tpd.Wildcard().withType(info.sig)
      typedApplyFunctionParams(dummy, args) map { res =>
        val resTyp = res.tpe
        val args = retriveAppliedArguments(res)
        tpd.AppliedTypeCon(info.symbol, args).withType(resTyp)
      }
    else
      Left(s"incorrect param num for type constructor ${info.name}")

  def typedApplyDataCon(info: DataConInfo, args: List[Expr])(using Context): TyperResult[tpd.Expr] =
    if args.length == info.paramNum then
      val dummy: tpd.Expr = tpd.Wildcard().withType(info.sig)
      typedApplyFunctionParams(dummy, args) map { res =>
        val resTyp = res.tpe
        val args = retriveAppliedArguments(res)
        tpd.AppliedDataCon(info.symbol, args).withType(resTyp)
      }
    else
      Left(s"incorrect param num for data constructor ${info.name}")

  def typedApplyFunction(fun: tpd.Expr, arg: Expr)(using Context): TyperResult[tpd.Expr] =
    fun.tpe match
      case funType @ tpd.PiType(argName, typ, resTyp) =>
        typed(arg, typ) map { arg =>
          val tpe = substBinder(funType, arg, resTyp)
          tpd.PiElim(fun, arg).withType(tpe)
        }
      case _ => Left(s"cannot apply value $fun of type ${fun.tpe}")

  def typedApplyFunctionParams(fun: tpd.Expr, arg: List[Expr])(using Context): TyperResult[tpd.Expr] =
    def recur(xs: List[Expr], acc: TyperResult[tpd.Expr]): TyperResult[tpd.Expr] = xs match
      case Nil => acc
      case x :: xs => recur(xs, acc.flatMap(typedApplyFunction(_, x)))
    recur(arg, Right(fun))

  def typedApply(fun: Expr, args: List[Expr])(using Context): TyperResult[tpd.Expr] =
    fun match
      case Var(funcName) =>
        ctx.lookup(funcName) match
          case None => Left(s"unknown name: $funcName when typing apply")
          case Some(info) => info match
            case info: TypeConInfo => typedApplyTypeCon(info, args)
            case info: DataConInfo => typedApplyDataCon(info, args)
            case _ =>
              typed(fun) flatMap { fun =>
                typedApplyFunctionParams(fun, args)
              }
            case _ => Left(s"not supported: $info as the function in typedApply")
      case _ =>
        typed(fun) flatMap { fun =>
          typedApplyFunctionParams(fun, args)
        }


object Typer:
  type TyperResult[+X] = Either[String, X]

