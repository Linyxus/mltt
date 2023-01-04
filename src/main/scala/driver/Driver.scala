package driver

import parser.Parser
import typer.Typer
import core.Context

object Driver:
  def check(source: String): Option[String] =
    Parser.parseProgram(source) match
      case Left(err) => Some(err)
      case Right(defs) =>
        val typer = new Typer
        val ctx = new Context
        typer.typedProgram(defs)(using ctx) match
          case Left(err) => Some(err)
          case Right(typed) => None

  def readFile(path: String): String =
    val content = io.Source.fromFile(path).getLines.mkString("\n")
    content

  def checkFile(path: String): Option[String] =
    check(readFile(path))

