package ast

case class DefDef(name: String, typ: Expr, body: Expr) extends Definition

