package core

import Symbols._
import ast.{TypedExprs => tpd}

case class ValInfo(sym: ValDefSymbol, typ: tpd.Expr, expr: tpd.Expr)

