package core

import ast.{TypedExprs => tpd}
import DataInfo._

object Symbols {
  sealed trait Symbol {
    type InfoType

    def info: InfoType
    def name: String

    override def toString(): String = s"Symbol($name)"
  }

  sealed trait ValSymbol extends Symbol {
    type InfoType = tpd.Expr
  }

  sealed trait DefSymbol extends Symbol {
    type InfoType <: DataInfo
  }

  trait DelayedInfo {
    type InfoType
    private var myInfo: InfoType | Null = null

    def info: InfoType = myInfo.nn

    def withInfo(info: InfoType): this.type =
      myInfo = info
      this
  }

  case class ParamSymbol(myName: String, myInfo: tpd.Expr) extends ValSymbol {
    type InfoType = tpd.Expr
    def info: InfoType = myInfo
    def name: String = myName
  }

  case class TypeConSymbol() extends DefSymbol with DelayedInfo {
    type InfoType = TypeConInfo
    def name: String = info.name
  }

  case class DataConSymbol() extends DefSymbol with DelayedInfo {
    type InfoType = DataConInfo
    def name: String = info.name
  }
}

