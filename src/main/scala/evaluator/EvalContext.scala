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

  def withBindings[T](bindings: List[(ValSymbol, Value)])(op: => T): T =
    val saved = store
    store = store ++ bindings
    val result = op
    store = saved
    result

  def fresh: EvalContext =
    val freshCtx = new EvalContext
    freshCtx.store = store
    freshCtx

  def addBinding(sym: ValSymbol, value: Value): Unit = store = store + (sym -> value)

  override def toString(): String = s"EvalContext($store)"

object EvalContext:
  def ctx(using EvalContext): EvalContext = summon[EvalContext]

