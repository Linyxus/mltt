package core

import ast.{TypedExprs => tpd}
import DataInfo._

object Symbols {
  protected var nextId: Int = 0

  sealed trait Symbol {
    type InfoType

    def info: InfoType
    def name: String

    override def toString(): String = s"Symbol($name)"

    private var myId: Int =
      nextId += 1
      nextId

    def symId: Int = myId
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

  case class ValDefSymbol(myName: String) extends ValSymbol {
    def info: InfoType = dealias.typ
    def name: String = myName

    private var myDef: ValInfo | Null = null
    def overwriteValInfo(info: ValInfo): Unit = myDef = info
    def dealias: ValInfo =
      assert(myDef ne null, s"ValDefSymbol $this does not have an info")
      myDef.nn

    def isDefined: Boolean = myDef ne null
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

