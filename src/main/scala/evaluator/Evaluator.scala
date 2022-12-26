package evaluator

import ast.TypedExprs
import TypedExprs._
import core._
import typer.Typer

import Evaluator._
import EvalContext._
import Value._
import Symbols._

class Evaluator:
  def eval(e: Expr)(using EvalContext): Value =
    e match
      case ValRef(sym) =>
        val res = ctx.lookup(sym)
        assert(res.isDefined)
        res.get
      case binder @ PiType(argName, argTyp, resTyp) =>
        Closure(ctx.fresh, ParamSymbol(argName, argTyp), resTyp)
      case binder @ PiIntro(argName, argTyp) => Closure(ctx.fresh, ParamSymbol(argName, argTyp), binder.body)
      case PiElim(func, arg) => evalApply(eval(func), eval(arg))
      case AppliedTypeCon(tycon, args) => AppliedType(tycon, args.map(eval(_)))
      case AppliedDataCon(datacon, args) => AppliedData(datacon, args.map(eval(_)))
      case Type(level) => TypeValue(level)
      case _ => assert(false, "non-supported: $e")

  def evalApply(fun: Value, arg: Value)(using EvalContext): Value =
    fun match
      case Closure(env, sym, body) =>
        ctx.withBinding(sym, arg)(eval(body))
      case NeutralValue(tp @ PiType(argName, argTyp, resTyp), neutral) =>
        val tpe: Expr = Typer.substBinder(tp, readBack(arg), resTyp)(using Context())
        NeutralValue(tpe, Neutral.Apply(neutral, arg))
      case _ => assert(false, fun)

  def readBack(value: Value): Expr = value match
    case AppliedType(tycon, args) => AppliedTypeCon(tycon, args.map(readBack))
    case AppliedData(dcon, args) => AppliedDataCon(dcon, args.map(readBack))
    case fun @ Closure(env, argSym, body) =>
      val argVal = NeutralValue(argSym.info, Neutral.Var(argSym))
      // val body1 = evalApply(fun, argVal)
      ???
    case _ => assert(false, value)


object Evaluator:
  ()

