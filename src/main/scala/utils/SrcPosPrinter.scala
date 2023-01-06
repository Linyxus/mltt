package utils

import ast.SrcPos

trait SrcPosPrinter:
  val source: String

  private lazy val lines: List[String] = source.linesWithSeparators.toList
  private lazy val lineLengths: List[Int] = lines.map(_.length)

  def posOf(pos: Int): (Int, Int) =
    @annotation.tailrec def recur(rem: Int, xs: List[Int], lineno: Int): (Int, Int) =
      xs match
        case Nil => (lineno, 0)
        case x :: xs =>
          if rem < x then (lineno, rem)
          else recur(rem - x, xs, lineno + 1)
    recur(pos, lineLengths, 0)

  def showSrcPos(srcPos: SrcPos, explanation: Option[String]): String =
    val (fromLine, fromCol) = posOf(srcPos.from)
    val (untilLine, untilCol) = posOf(srcPos.until)
    val numLines = untilLine - fromLine + 1

    def padLineNumber(lineno: Int): String =
      val mWidth = (untilLine + 1).toString.length
      val res = (lineno + 1).toString
      " " * (mWidth - res.length) + res

    val sb = StringBuilder()

    def showLineWithMarker(lineno: Int, offset: Int, len: Int, explanation: Option[String]): Unit =
      val prefix = " " + padLineNumber(lineno) + " | "
      val line = if lineno < lines.length then lines(lineno) else "\n"
      sb ++= prefix + line
      val leadingSpaces = " " * (prefix.length + offset)
      val markerStr = "^" * len
      sb ++= leadingSpaces + markerStr + "\n"
      explanation.map(x => sb ++= leadingSpaces + x + "\n")

    def atLeastOne(n: Int): Int = if n <= 1 then 1 else n

    if numLines <= 1 then
      showLineWithMarker(fromLine, fromCol, atLeastOne(untilCol - fromCol), explanation)
    else
      def showFirstLine =
        showLineWithMarker(fromLine, fromCol, atLeastOne(lineLengths(fromLine) - fromCol - 1), None)
      def showLastLine =
        showLineWithMarker(untilLine, 0, atLeastOne(untilCol), explanation)
      def showMiddleLine(lineno: Int) =
        showLineWithMarker(lineno, 0, atLeastOne(lineLengths(lineno) - 1), None)

      showFirstLine
      (fromLine + 1).until(untilLine).foreach(showMiddleLine)
      showLastLine

    sb.result

