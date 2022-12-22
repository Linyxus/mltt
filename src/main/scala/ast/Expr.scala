package ast

sealed trait Expr {
  override def toString(): String = this match
    case Var(name) => name
    case Pi(arg, typ, resTyp) => s"(($arg:$typ) -> $resTyp)"
    case PiIntro(arg, body) => s"(\\$arg. $body)"
    case Apply(func, args) => s"$func(${args.map(_.toString).mkString(", ")})"
    case ApplyTypeCon(name, args) => s"$name(${args.map(_.toString).mkString(", ")})"
    case ApplyDataCon(name, args) => s"$name(${args.map(_.toString).mkString(", ")})"
    case Match(scrutinee, cases) => s"($scrutinee) match (${cases.map(_.toString).mkString("; ")})"
    case Type(level) => s"Type($level)"
    case Wildcard => "_"
}

case class Var(name: String) extends Expr

case class Pi(arg: String, typ: Expr, resTyp: Expr) extends Expr

case class PiIntro(arg: String, body: Expr) extends Expr

case class Apply(func: Expr, args: List[Expr]) extends Expr

case class ApplyTypeCon(name: String, args: List[Expr]) extends Expr

case class ApplyDataCon(name: String, args: List[Expr]) extends Expr

case class CaseDef(pat: ApplyDataCon, body: Expr)

case class Match(scrutinee: Expr, cases: List[CaseDef]) extends Expr

enum Level {
  case LZero
  case LSucc(pred: Level)

  def lub(other: Level): Level =
    (this, other) match
      case (LZero, b) => b
      case (a, LZero) => a
      case (LSucc(a), LSucc(b)) => LSucc(a lub b)
}

case class Type(level: Level) extends Expr

case object Wildcard extends Expr

