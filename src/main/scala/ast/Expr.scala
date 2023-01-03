package ast

sealed trait Expr {
  override def toString(): String = this match
    case Var(name) => name
    case Pi(arg, typ, resTyp, imp) =>
      def maybeUsing: String = if imp then "using " else ""
      s"(($maybeUsing$arg:$typ) -> $resTyp)"
    case PiIntro(arg, body) => s"(\\$arg. $body)"
    case Apply(func, args, imp) => s"$func(${args.map(_.toString).mkString(", ")})"
    case ApplyTypeCon(name, iargs, args) => s"$name(${args.map(_.toString).mkString(", ")})"
    case ApplyDataCon(name, iargs, args) => s"$name(${args.map(_.toString).mkString(", ")})"
    case Match(scrutinee, cases) => s"($scrutinee) match (${cases.map(_.toString).mkString("; ")})"
    case Type(level) => s"Type($level)"
    case Level() => s"Level"
    case LZero() => s"lzero"
    case LSucc(pred) => s"lsucc($pred)"
    case LLub(l1, l2) => s"$l1 ⊔ $l2"
    case Undefined() => "???"
    case Wildcard => "_"
    case Block(ddefs, expr) => s"Block($ddefs, $expr)"
}

case class Var(name: String) extends Expr

case class Pi(arg: String, typ: Expr, resTyp: Expr, imp: Boolean) extends Expr

case class PiIntro(arg: String, body: Expr) extends Expr

case class Apply(func: Expr, args: List[Expr], imp: Boolean) extends Expr

case class ApplyTypeCon(name: String, iargs: List[Expr], args: List[Expr]) extends Expr

case class ApplyDataCon(name: String, iargs: List[Expr], args: List[Expr]) extends Expr

case class CaseDef(pat: ApplyDataCon, body: Option[Expr])

case class Match(scrutinee: Expr, cases: List[CaseDef]) extends Expr

case class Block(ddefs: List[DefDef], expr: Expr) extends Expr

case class Level() extends Expr

case class LZero() extends Expr

case class LSucc(pred: Expr) extends Expr

case class LLub(e1: Expr, e2: Expr) extends Expr

case class Type(level: Expr) extends Expr

case class Undefined() extends Expr

case object Wildcard extends Expr

