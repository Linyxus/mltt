package evaluator

import ast.TypedExprs
import TypedExprs._
import core.Symbols._
import ast.Level

sealed trait Value

object Value:
  type Binder = PiIntro | PiType
  case class Closure(env: EvalContext, arg: ParamSymbol, body: Expr) extends Value

  case class AppliedType(tycon: TypeConSymbol, args: List[Value]) extends Value
  case class AppliedData(dcon: DataConSymbol, args: List[Value]) extends Value

  case class NeutralValue(tpe: Expr, neutral: Neutral) extends Value

  case class TypeValue(level: Level) extends Value

  sealed trait Neutral
  object Neutral:
    case class Var(sym: ValSymbol) extends Neutral
    case class Apply(fun: Neutral, arg: Value) extends Neutral

