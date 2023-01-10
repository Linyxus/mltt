package core

import ast.TypedExprs._
import utils.trace

class ExprHasher extends ExprTraverser:
  private var resultStack: List[String] = Nil

  private var binderStack: List[Int] = Nil

  def conclude(s: String): Unit =
    resultStack = s :: resultStack

  override def traverse(e: Expr): Unit =
    val dep = resultStack.length
    super.traverse(e)
    assert(resultStack.length == dep + 1)

  def apply(e: Expr): String = trace(s"hash($e)") {
    traverse(e)
    val res = resultStack.head
    resultStack = resultStack.tail
    res
  }

  override def traverseValRef(e: ValRef): Unit =
    conclude(s"@${e.sym.symId}")

  override def traverseUVarRef(e: UVarRef): Unit =
    if e.info.instantiated then traverse(e.info.instance)
    else conclude(s"?${e.info.name}")

  def withinBinder[T](binder: PiType | PiIntro | CaseDef)(op: => T) =
    def getId: Int = binder match
      case e: Expr => e.exprId
      case cd: CaseDef => cd.exprId
    val saved = binderStack
    binderStack = getId :: binderStack
    val result = op
    binderStack = saved
    result

  def debruijnIndexOf(binder: PiType | PiIntro | CaseDef): Option[Int] =
    def getId: Int = binder match
      case e: Expr => e.exprId
      case cd: CaseDef => cd.exprId
    @annotation.tailrec def recur(xs: List[Int], now: Int): Option[Int] =
      xs match
        case Nil => None
        case x :: xs => if x == getId then Some(now) else recur(xs, now + 1)
    recur(binderStack, 0)

  override def traversePiType(e: PiType): Unit =
    val typ = this(e.argTyp)
    withinBinder(e) {
      conclude(s"($typ -> ${this(e.resTyp)})")
    }

  def showParamRef(e: ParamRef, showOp: (x: Int) => String = _.toString): String =
    debruijnIndexOf(e.binder) match
      case None => e.toString
      case Some(idx) => showOp(idx)

  override def traversePiTypeParamRef(e: PiTypeParamRef): Unit =
    conclude(showParamRef(e))

  override def traversePiIntro(e: PiIntro): Unit =
    val typ = this(e.argTyp)
    withinBinder(e) {
      conclude(s"($typ => ${this(e.body)})")
    }

  override def traversePiElim(e: PiElim): Unit =
    conclude(s"(${this(e.func)} ${this(e.arg)})")

  override def traverseAppliedDataCon(e: AppliedDataCon): Unit =
    conclude(s"${e.datacon.name}(${e.args.map(this(_)).mkString(",")})")

  override def traverseAppliedTypeCon(e: AppliedTypeCon): Unit =
    conclude(s"${e.tycon.name}(${e.args.map(this(_)).mkString(",")})")

  override def traverseMatch(e: Match): Unit =
    def showCase(cdef: CaseDef): String =
      withinBinder(cdef) {
        s"${cdef.pat.datacon.name}==>${this(cdef.body)}"
      }
    val cases = e.cases.map(showCase)
    conclude(s"(${this(e.scrutinee)} match {${cases.mkString(",")}})")

  override def traversePatternBoundParamRef(e: PatternBoundParamRef): Unit =
    conclude(showParamRef(e, showOp = idx => s"$idx.${e.paramIdx}"))

  override def traverseType(e: Type): Unit = conclude(s"Type(${this(e.level)})")

  override def traverseLevel(e: Level): Unit = conclude("Level")

  override def traverseLZero(e: LZero): Unit = conclude("lzero")

  override def traverseLSucc(e: LSucc): Unit = conclude(s"lsuc")

  override def traverseLLub(e: LLub): Unit = conclude(s"llub(${this(e.l1)},${this(e.l2)})")

  override def traverseWildcard(e: Wildcard): Unit = conclude(s"_")

  override def traversePiIntroParamRef(e: PiIntroParamRef): Unit = conclude(showParamRef(e))

object ExprHasher:
  def hash(e: Expr): String =
    val hasher = ExprHasher()
    hasher(e)
