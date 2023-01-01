package typer

import core._
import ast.TypedExprs._
import Symbols._
import Typer.TyperResult

trait ConstraintSolving:
  def constraint(using Context): EqConstraint
  def constraint_=(c: EqConstraint)(using Context): Unit
  def normalise(e: Expr)(using Context): Expr

  def addEquality(e1: Expr, e2: Expr)(using Context): TyperResult[Unit] =
    def checkParams(p: ParamSymbol, q: ParamSymbol): TyperResult[Unit] =
      if constraint.isSame(p, q) then Right(())
      else
        constraint = constraint.addParamEq(p, q)
        (constraint.instanceOf(p), constraint.instanceOf(q)) match
          case (Some(ep), Some(eq)) =>
            recur(ep, eq)
          case (Some(ep), None) =>
            constraint = constraint.instantiate(q, ep)
            Right(())
          case (None, Some(eq)) =>
            constraint = constraint.instantiate(p, eq)
            Right(())
          case _ =>
            Right(())

    def checkInstance(p: ParamSymbol, e: Expr): TyperResult[Unit] =
      constraint.instanceOf(p) match
        case None =>
          constraint = constraint.instantiate(p, e)
          Right(())
        case Some(e1) => recur(e1, e)

    def recur(e1: Expr, e2: Expr): TyperResult[Unit] =
      (e1, e2) match
        case (ValRef(p1: ParamSymbol), ValRef(p2: ParamSymbol)) => checkParams(p1, p2)
        case (ValRef(p1: ParamSymbol), e2) => checkInstance(p1, e2)
        case (e1, ValRef(p2: ParamSymbol)) => checkInstance(p2, e1)
        case (AppliedDataCon(sym1, args1), AppliedDataCon(sym2, args2)) =>
          if sym1 ne sym2 then Left(s"absurd equality $e1 === $e2")
          else Typer.collectAll(args1.zip(args2).map(recur(_, _))).map(_ => ())
        case (AppliedTypeCon(sym1, args1), AppliedTypeCon(sym2, args2)) =>
          if sym1 ne sym2 then Left(s"absurd equality $e1 === $e2")
          else Typer.collectAll(args1.zip(args2).map(recur(_, _))).map(_ => ())
        case (e1, e2) =>
          if e1 == e2 then Right(())
          else
            constraint = constraint.addComplexEq(e1, e2)
            Right(())

    recur(normalise(e1), normalise(e2))

