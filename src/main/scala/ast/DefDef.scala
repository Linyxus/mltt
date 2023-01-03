package ast

case class DefDef(name: String, typ: Expr, body: Option[Expr]) extends Definition

