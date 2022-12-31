package evaluator

import ast.TypedExprs
import TypedExprs._
import core.Symbols._

sealed trait Value {
  private var myTpe: Expr | Null = null
  def tpe: Expr = myTpe.nn
  def withType(tp: Expr): this.type =
    myTpe = tp
    this
  def hasType: Boolean = myTpe ne null
}

object Value:
  case class Closure(env: EvalContext, arg: ParamSymbol, body: Expr) extends Value {
    override def toString(): String = s"Closure($arg, $body)"
  }
  case class PiValue(resTyp: Closure) extends Value

  case class AppliedType(tycon: TypeConSymbol, args: List[Value]) extends Value
  case class AppliedData(dcon: DataConSymbol, args: List[Value]) extends Value

  case class NeutralValue(neutral: Neutral) extends Value

  case class LevelValue() extends Value
  sealed trait LevelVal extends Value
  case class LZeroVal() extends LevelVal
  case class LSuccVal(pred: Value) extends LevelVal

  case class TypeValue(level: Value) extends Value

  sealed trait Neutral
  object Neutral:
    case class Wildcard() extends Neutral
    case class Var(sym: ValSymbol) extends Neutral
    case class Apply(fun: NeutralValue, arg: Value) extends Neutral
    case class LevelLub(l: NeutralValue | LevelVal, r: NeutralValue | LevelVal) extends Neutral
    case class Match(scrut: NeutralValue, cases: List[CaseDef]) extends Neutral

