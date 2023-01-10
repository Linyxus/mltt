package core.messages

import core.Context
import evaluator.Reducer
import Context.ctx
import ast.{TypedExprs => tpd}

abstract class Message:
  def level: Message.Level = Message.Level.Error
  def show(using Context): String

object Message:
  enum Level:
    case Error
    case Warning
    case Info

  class HoleInfo(context: Context, goal: tpd.Expr) extends Message:
    override def level: Level = Level.Info

    private var cache: String | Null = null

    def show(using Context): String =
      if cache ne null then cache
      else
        val sb = StringBuilder()
        sb ++= "Goal\n"
        sb ++= "----\n"
        sb ++= "\n"
        sb ++= s"  ${Reducer.reduce(goal)(using context).show}\n"
        sb ++= s"\n"
        sb ++= s"Variables\n"
        sb ++= s"---------\n"
        sb ++= context.description((e: tpd.Expr) => Reducer.reduce(e)(using context).show)
        sb ++= s"\n"
        sb ++= s"Equalities\n"
        sb ++= s"----------\n"
        sb ++= context.constraint.show ++ "\n"
        cache = sb.result()
        cache

