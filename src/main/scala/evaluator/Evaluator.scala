package evaluator

import ast.TypedExprs
import TypedExprs._
import core._
import typer.Typer
import utils.trace

import Evaluator._
import EvalContext._
import Value._
import Symbols._

object Evaluator:
  def eval(e: Expr)(using EvalContext): Value = trace(s"eval($e)") {
    val res = e match
      case ValRef(sym) =>
        val res = ctx.lookup(sym)
        assert(res.isDefined, s"non-defined sym: $sym, eval context: $ctx")
        res.get
      case binder @ PiType(argName, argTyp, resTyp) =>
        val sym = ParamSymbol(argName, normalise(argTyp))
        val resTyp1 = Typer.substBinder(binder, ValRef(sym), resTyp)
        val closure = Closure(ctx.fresh, sym, resTyp1)
        PiValue(closure)
      case binder @ PiIntro(argName, argTyp) =>
        val sym = ParamSymbol(argName, argTyp)
        val body1 = Typer.substBinder(binder, ValRef(sym), binder.body)
        Closure(ctx.fresh, sym, body1)
      case PiElim(func, arg) => evalApply(eval(func), eval(arg))
      case AppliedTypeCon(tycon, args) => AppliedType(tycon, args.map(eval(_)))
      case AppliedDataCon(datacon, args) => AppliedData(datacon, args.map(eval(_)))
      case e @ Match(scrutinee) => evalMatch(eval(scrutinee), e.cases, e.tpe)
      case Type(level) => TypeValue(eval(level))
      case LZero() => LZeroVal()
      case LSucc(e) => LSuccVal(eval(e))
      case LLub(l1, l2) => evalLevelLub(eval(l1), eval(l2))
      case Wildcard() => NeutralValue(Neutral.Wildcard())
      case Level() => LevelValue()
      case _ => assert(false, s"non-supported: $e")
    res.withType(e.tpe)
  }

  def evalApply(fun: Value, arg: Value): Value =
    fun match
      case Closure(env, sym, body) =>
        env.withBinding(sym, arg)(eval(body)(using env))
      case nv @ NeutralValue(neutral) =>
        val tp: PiType = nv.tpe.asInstanceOf
        val PiType(argName, argTyp, resTyp) = tp
        val tpe: Expr = Typer.substBinder(tp, readBack(arg), resTyp)
        NeutralValue(Neutral.Apply(nv, arg)).withType(tpe)
      case _ => assert(false, fun)

  def evalCase(cdef: CaseDef, argsOpt: Option[List[Value]])(using EvalContext): (Value, List[ParamSymbol]) =
    @annotation.tailrec def buildParamSyms(ps: List[(String, Expr)], idx: Int, acc: List[ParamSymbol]): List[ParamSymbol] = ps match
      case Nil => acc.reverse
      case (pname, ptyp) :: ps =>
        val sym = ParamSymbol(pname, ptyp)
        val substitutor = new ExprMap:
          override def mapPatternBoundParamRef(e: PatternBoundParamRef): Expr =
            if (e.binder.exprId == cdef.exprId) && e.paramIdx == idx then ValRef(sym)
            else super.mapPatternBoundParamRef(e)
        buildParamSyms(ps.map((name, typ) => (name, substitutor(typ))), idx + 1, sym :: acc)
    val psyms = buildParamSyms(cdef.pat.argNames.zip(cdef.pat.argTyps), 0, Nil)
    val substitutor = new ExprMap:
      override def mapPatternBoundParamRef(e: PatternBoundParamRef): Expr =
        if e.binder.exprId == cdef.exprId then ValRef(psyms(e.paramIdx)) else super.mapPatternBoundParamRef(e)
      // override def apply(e: Expr): Expr =
      //   println(s"apply($e)")
      //   super.apply(e)
    val body1 = substitutor(cdef.body)
    val args = argsOpt getOrElse {
      psyms.map(sym => NeutralValue(Neutral.Var(sym)).withType(sym.info))
    }
    (ctx.withBindings(psyms.zip(args))(eval(body1)), psyms)

  def evalMatch(scrut: Value, cases: List[CaseDef], tp: Expr)(using EvalContext) = scrut match
    case AppliedData(dcon, args) =>
      @annotation.tailrec def recur(cs: List[CaseDef]): Value =
        cs match
          case Nil => assert(false)
          case cdef :: cs =>
            if cdef.pat.datacon.name == dcon.name then
              evalCase(cdef, Some(args))._1
            else recur(cs)
      recur(cases)
    case scrut @ NeutralValue(neu) => NeutralValue(Neutral.Match(scrut, cases)).withType(tp)
    case _ => assert(false, scrut)

  def evalLevelLub(l1: Value, l2: Value): Value =
    (l1, l2) match
      case (LZeroVal(), r) => r
      case (l, LZeroVal()) => l
      case (LSuccVal(l), LSuccVal(r)) => LSuccVal(evalLevelLub(l, r)).withType(Level())
      case (l: (NeutralValue | LevelVal), r: (NeutralValue | LevelVal)) => NeutralValue(Neutral.LevelLub(l, r)).withType(Level())
      case _ => assert(false, (l1, l2))

  def readBack(value: Value): Expr = trace(s"readBack($value) with ${value.tpe}") {
    (value.tpe, value) match
      case (tpe, AppliedType(tycon, args)) => AppliedTypeCon(tycon, args.map(readBack)).withType(tpe)
      case (tpe, AppliedData(dcon, args)) => AppliedDataCon(dcon, args.map(readBack)).withType(tpe)
      case (binder @ PiType(argName, argTyp, resTyp), fun) =>
        val argSym = ParamSymbol(argName, argTyp)
        val argVal = NeutralValue(Neutral.Var(argSym)).withType(argTyp)
        val body = readBack(evalApply(fun, argVal))

        val paramRef = PiIntroParamRef()
        val body1 = Typer.abstractSymbol(argSym, paramRef, body)
        val newFunc = PiIntro(argName, argTyp).withBody(body1.withTypeUnchecked(resTyp)).withType(binder)
        paramRef.overwriteBinder(newFunc)
        newFunc
      case (tp, PiValue(fun @ Closure(env, argSym, body))) =>
        val argVal = NeutralValue(Neutral.Var(argSym)).withType(argSym.info)
        val body = readBack(evalApply(fun, argVal))
        val pref = PiTypeParamRef()
        val body1 = Typer.abstractSymbol(argSym, pref, body)
        val pi = PiType(argSym.name, argSym.info, body1).withType(tp)
        pref.overwriteBinder(pi)
        pi
      case (tp, NeutralValue(neu)) => readBack(neu, tp)
      case (tp, LZeroVal()) => LZero().withTypeUnchecked(tp)
      case (tp, LSuccVal(e)) => LSucc(readBack(e)).withTypeUnchecked(tp)
      case (tp, TypeValue(l)) => Type(readBack(l))
      case (tp, LevelValue()) => Level()
      case _ => assert(false, value)
  }

  def readBack(neu: Neutral, tp: Expr): Expr = trace(s"readBack($neu) with $tp") {
    neu match
      case Neutral.Wildcard() => Wildcard().withType(tp)
      case Neutral.Var(sym) => ValRef(sym)
      case Neutral.Apply(fun, arg) =>
        PiElim(readBack(fun.neutral, fun.tpe), readBack(arg)).withType(tp)
      case Neutral.LevelLub(l1, l2) =>
        LLub(readBackLevel(l1), readBackLevel(l2))
      case Neutral.Match(scrut, cases) =>
        ???
  }

  def readBackLevel(l: NeutralValue | LevelVal): Expr = l match
    case nv: NeutralValue => readBack(nv.neutral, nv.tpe)
    case nv: LevelVal => readBack(nv)

  def normalise(e: Expr)(using EvalContext): Expr =
    readBack(eval(e))

  def evalDef(sym: ValSymbol, e: Expr)(using EvalContext): Value =
    val res = eval(e)
    ctx.addBinding(sym, res)
    res match
      case Closure(env, arg, body) =>
        env.addBinding(sym, res)
      case _ =>
    res

