package ast

import core.Symbols._
import ast.Level

object TypedExprs {
  sealed trait Expr {
    private var myTpe: Expr | Null = null
    def tpe: Expr = myTpe

    def withType(tp: Expr): this.type =
      myTpe = tp
      this
  }

  case class VarRef(sym: Symbol)

  case class PiType(argName: String, argTyp: Expr, resTyp: Expr) extends Expr
  case class PiTypeParamRef(binder: PiType) extends Expr

  case class PiIntro(argName: String, argTyp: Expr, body: Expr) extends Expr
  case class PiIntroParamRef(binder: PiIntro) extends Expr

  case class PiElim(func: Expr, arg: Expr) extends Expr

  case class AppliedTypeCon(tycon: TypeConSymbol, args: List[Expr]) extends Expr
  case class AppliedDataCon(datacon: DataConSymbol, args: List[Expr]) extends Expr

  case class Pattern(datacon: DataConSymbol, args: List[String])
  case class CaseDef(patmat: Match, pat: Pattern, body: Expr)
  case class Match(scrutinee: Expr, cases: List[CaseDef]) extends Expr

  case class PatternBoundParamRef(binder: Match, paramIdx: Int)
  case class Type(level: Level) extends Expr
}

