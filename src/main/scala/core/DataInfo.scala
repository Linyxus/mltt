package core

import ast._
import ast.{TypedExprs => tpd}
import scala.annotation.tailrec
import ast.TypedExprs.PiType
import ast.TypedExprs.PiTypeParamRef
import ast.TypedExprs.PiIntro
import ast.TypedExprs.PiIntroParamRef
import ast.TypedExprs.PiElim
import ast.TypedExprs.AppliedTypeCon
import ast.TypedExprs.AppliedDataCon
import ast.TypedExprs.Match
import ast.TypedExprs.Type

sealed trait DataInfo

object DataInfo:
  case class TypeConInfo(
    name: String,
    sig: tpd.Expr,
    constructorsCompleter: TypeConInfo => List[DataConInfo]) extends DataInfo {
    val constructors: List[DataConInfo] = constructorsCompleter(this)
  }
  case class DataConInfo(name: String, dataType: TypeConInfo, sig: tpd.Expr) extends DataInfo {
    def paramNum: Int =
      @tailrec def recur(e: tpd.Expr, acc: Int): Int = e match
        case tpd.PiType(arg, typ, resTyp) => recur(resTyp, acc + 1)
        case _ => acc
      recur(sig, 0)

    def paramTypeOf(idx: Int): tpd.Expr =
      @tailrec def recur(e: tpd.Expr, acc: Int): tpd.Expr = e match
        case PiType(argName, argTyp, resTyp) =>
          if acc <= 0 then
            argTyp
          else recur(resTyp, acc - 1)
        case _ => assert(false)
      recur(sig, idx)
  }

