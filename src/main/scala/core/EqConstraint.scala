package core

import ast.TypedExprs._
import Symbols._
import evaluator.Reducer
import EqConstraint._

case class EqConstraint(
  disjointSet: DisjointSet,
  instances: Map[SymbolIdentityKey, Expr],
  otherEq: List[(Expr, Expr)]):

  def addComplexEq(l: Expr, r: Expr): EqConstraint =
    copy(otherEq = (l, r) :: otherEq)

  def instantiate(sym: ParamSymbol, e: Expr): EqConstraint =
    val psym = disjointSet.reprOf(sym)
    val key = SymbolIdentityKey(psym)
    // assert(!instances.contains(key))
    copy(instances = instances + (key -> e))

  def addParamEq(p1: ParamSymbol, p2: ParamSymbol): EqConstraint =
    copy(disjointSet = disjointSet.addEq(p1, p2))

  def isSame(p1: ParamSymbol, p2: ParamSymbol): Boolean =
    disjointSet.isSame(p1, p2)

  def instanceOf(p: ParamSymbol): Option[Expr] =
    val q = disjointSet.reprOf(p)
    val key = SymbolIdentityKey(q)
    instances.get(key)

  def reprOf(p: ParamSymbol): ParamSymbol = disjointSet.reprOf(p)

object EqConstraint:
  case class SymbolIdentityKey(symId: Int, symbol: ParamSymbol)

  object SymbolIdentityKey:
    def apply(symbol: ParamSymbol): SymbolIdentityKey = SymbolIdentityKey(symbol.symId, symbol)

  class DisjointSet(next: Map[Int, ParamSymbol]):
    def nextOf(x: ParamSymbol): ParamSymbol = next.get(x.symId).getOrElse(x)
    def reprOf(x: ParamSymbol): ParamSymbol =
      if nextOf(x) eq x then x else reprOf(nextOf(x))

    def isSame(x: ParamSymbol, y: ParamSymbol): Boolean =
      reprOf(x) eq reprOf(y)

    def addEq(x: ParamSymbol, y: ParamSymbol): DisjointSet =
      val px = reprOf(x)
      val py = reprOf(y)
      if px eq py then this else new DisjointSet(next + (px.symId -> py))
