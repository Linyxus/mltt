package utils

object trace:
  private var indentLevel: Int = 0

  private def indentStr: String = "  " * indentLevel

  def apply[T](question: String, showOp: Any = null)(op: => T): T = op

  def force[T](question: String, showOp: (x: T) => String = (x: T) => x.toString)(op: => T): T =
    println(indentStr + "==> " + question + "?")
    val saved = indentLevel
    try
      indentLevel += 1
      val result = op
      indentLevel -= 1
      println(indentStr + "<== " + question + " = " + showOp(result))
      result
    finally
      indentLevel = saved

