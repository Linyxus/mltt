package driver

import parser.Parser
import typer.Typer
import core.Context
import core.messages._

object Driver:
  def check(source: String): List[String] =
    val ctx = new Context
    given Context = ctx.setSource(source).setupSrcPosPrinter
    Parser.parseProgram(source) match
      case Left(err) => err.show :: Nil
      case Right(defs) =>
        val typer = new Typer
        typer.typedProgram(defs) match
          case Left(err) => err.show :: Nil
          case Right(typed) => Nil

  def readFile(path: String): String =
    val content = io.Source.fromFile(path).getLines.mkString("\n")
    content

  def checkFile(path: String): List[String] =
    check(readFile(path))

