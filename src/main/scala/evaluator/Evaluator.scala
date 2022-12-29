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
  def eval(e: Expr)(using EvalContext): Value =
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
      case Type(level) => TypeValue(eval(level))
      case LZero() => LZeroVal()
      case LSucc(e) => LSuccVal(eval(e))
      case LLub(l1, l2) => evalLevelLub(eval(l1), eval(l2))
      case Wildcard() => NeutralValue(Neutral.Wildcard())
      case Level() => LevelValue()
      case _ => assert(false, s"non-supported: $e")
    res.withType(e.tpe)

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
  }

  def readBackLevel(l: NeutralValue | LevelVal): Expr = l match
    case nv: NeutralValue => readBack(nv.neutral, nv.tpe)
    case nv: LevelVal => readBack(nv)

  def normalise(e: Expr)(using EvalContext): Expr =
    readBack(eval(e))

  def evalDef(sym: ValSymbol, e: Expr)(using EvalContext): Value =
    val res = eval(e)
    ctx.addBinding(sym, res)
    res

