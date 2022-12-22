package core

import ast.{TypedExprs => tpd}
import DataInfo._

object Symbols {
  sealed trait Symbol {
    type InfoType

    def info: InfoType
  }

  case class PiTypeParamSymbol(binder: tpd.PiType) extends Symbol {
    type InfoType = tpd.Expr
    def info: InfoType = binder.argTyp
    def name: String = binder.argName
  }

  case class PiIntroParamSymbol(binder: tpd.PiIntro) extends Symbol {
    type InfoType = tpd.Expr
    def info: InfoType = binder.argTyp
    def name: String = binder.argName
  }

  case class TypeConSymbol(tycon: TypeConInfo) extends Symbol {
    type InfoType = TypeConInfo
    def info: InfoType = tycon
  }

  case class DataConSymbol(datacon: DataConInfo) extends Symbol {
    type InfoType = DataConInfo
    def info: InfoType = datacon
  }

  case class PatternBoundSymbol(mcase: tpd.CaseDef, paramIdx: Int) extends Symbol {
    type InfoType = tpd.Expr
    def info: InfoType = mcase.pat.datacon.info.paramTypeOf(paramIdx)
    def name: String = mcase.pat.args(paramIdx)
  }
}

