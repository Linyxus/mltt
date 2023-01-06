package core.messages

import ast.{WithPos, SrcPos, TypedExprs => tpd}
import core.Context
import Context._
import core.DataInfo._
import core.UVarInfo

object Errors:
  class ParseError(msg: String) extends Message, WithPos:
    def show(using Context): String =
      ctx.showSrcPos(srcPos, Some(msg))

  abstract class TypeError extends Message, WithPos:
    def msg: Option[String]
    def more: Option[String]
    def show(using Context): String =
      var res = ctx.showSrcPos(srcPos, msg)
      more.map(more => res += more + "\n")
      "Type error:\n" ++ res

  class TypeMismatch(e: tpd.Expr, pt: tpd.Expr, tp1: tpd.Expr, tp2: tpd.Expr) extends TypeError:
    setPos(e.srcPos)
    def msg: Option[String] = Some(s"type mismatch")
    def more: Option[String] =
      val src = s"""  actual: ${e.tpe.show}
                |  expected: ${pt.show}
                |  the part that mismatches: ${tp1.show} vs ${tp2.show}
                |when typing expression ${e.show}
                |""".stripMargin
      Some(src)

  class ConstructorNotFullyApplied(srcPos: SrcPos, info: TypeConInfo | DataConInfo, current: tpd.Expr) extends TypeError:
    setPos(srcPos)
    val isType: Boolean = info match
      case _: TypeConInfo => true
      case _ => false

    val kindStr: String = if isType then "type" else "data"
    val sig: tpd.Expr = info match
      case info: TypeConInfo => info.sig
      case info: DataConInfo => info.sig
    val name: String = info match
      case info: TypeConInfo => info.name
      case info: DataConInfo => info.name

    def msg: Option[String] = Some(s"$kindStr constructor is not fully-applied")
    def more: Option[String] =
      val str = s"""$name's signature is ${sig.show}, and currently the application is typed as
                |
                |    ${current.show}
                |""".stripMargin
      Some(str)

  class UnsolvedUVar(site: SrcPos, uvars: List[UVarInfo]) extends TypeError:
    setPos(site)
    def msg: Option[String] = None
    def more: Option[String] = Some(s"Failed to solve unification variables:")

    override def show(using Context): String =
      def showUVar(uv: UVarInfo): String =
        ctx.showSrcPos(uv.creator.site, Some(s"${uv.name}, which is created when inferencing ${uv.creator.reason} here"))
      val res = super.show
      res ++ uvars.map(showUVar).mkString("")

  class OtherTypeError(message: String) extends TypeError:
    def msg: Option[String] = Some(message)
    def more: Option[String] = None

