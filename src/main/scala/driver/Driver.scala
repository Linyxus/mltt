package driver

import parser.Parser
import typer.Typer
import core.Context
import Context._
import core.messages._

object Driver:
  def typecheck(using Context): List[Message] =
    val source = ctx.currentSource
    Parser.parseProgram(source) match
      case Left(err) => err :: ctx.messages
      case Right(defs) =>
        val typer = new Typer
        typer.typedProgram(defs) match
          case Left(err) => err :: ctx.messages
          case Right(typed) => ctx.messages

  def readFile(path: String): String =
    val content = io.Source.fromFile(path).getLines.mkString("\n")
    content

  def getContext(source: String): Context =
    Context().setSource(source).setupSrcPosPrinter

  def contextFromPath(path: String): Context =
    getContext(readFile(path))

  def typecheckFile(path: String): List[Message] =
    typecheck(using contextFromPath(path))

  def runTypecheck(source: String): Unit =
    given Context = getContext(source)
    val msgs = typecheck
    msgs.foreach { msg =>
      println(msg.show)
    }

