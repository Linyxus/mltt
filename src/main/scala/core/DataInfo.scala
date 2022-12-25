package core

import ast._
import ast.{TypedExprs => tpd}
import Symbols._
import scala.annotation.tailrec

sealed trait DataInfo

object DataInfo:
  trait ParamHandling {
    val sig: tpd.Expr

    def paramNum: Int =
      @tailrec def recur(e: tpd.Expr, acc: Int): Int = e match
        case tpd.PiType(arg, typ, resTyp) => recur(resTyp, acc + 1)
        case _ => acc
      recur(sig, 0)

    def paramTypeOf(idx: Int): tpd.Expr =
      @tailrec def recur(e: tpd.Expr, acc: Int): tpd.Expr = e match
        case tpd.PiType(argName, argTyp, resTyp) =>
          if acc <= 0 then
            argTyp
          else recur(resTyp, acc - 1)
        case _ => assert(false)
      recur(sig, idx)
  }

  case class TypeConInfo(
    name: String,
    symbol: TypeConSymbol,
    sig: tpd.Expr,
    constructorsCompleter: TypeConInfo => List[DataConInfo]) extends DataInfo with ParamHandling {
    val constructors: List[DataConInfo] = constructorsCompleter(this)

    override def toString(): String = s"TypeConInfo($symbol, $sig, $constructors)"
  }

  case class DataConInfo(name: String, symbol: DataConSymbol, dataType: TypeConInfo, sig: tpd.Expr) extends DataInfo with ParamHandling {
    override def toString(): String = s"DataConInfo($symbol, $sig)"
  }

