package evaluator

import core.Symbols._

class EvalContext:
  private var store: Map[ValSymbol, Value] = Map.empty

  def lookup(sym: ValSymbol): Option[Value] = store.get(sym)

  def withBinding[T](sym: ValSymbol, value: Value)(op: => T): T =
    val saved = store
    store = store + (sym -> value)
    val result = op
    store = saved
    result

  def fresh: EvalContext =
    val freshCtx = new EvalContext
    freshCtx.store = store
    freshCtx

object EvalContext:
  def ctx(using EvalContext): EvalContext = summon[EvalContext]

