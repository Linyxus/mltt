package ast

object Commands:
  case class Normalise(expr: Expr) extends Definition

