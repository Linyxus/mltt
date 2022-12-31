package evaluator

import ast.TypedExprs._
import core.Symbols._
import typer.Typer
import utils.trace

class Reducer extends ExprMap:
  private var isReduced: List[Boolean] = Nil

  def conclude(isReduced: Boolean)(e: Expr): e.type =
    this.isReduced = isReduced :: this.isReduced
    e

  def reduced(e: Expr): e.type = conclude(true)(e)

  def nonReduced(e: Expr): e.type = conclude(false)(e)

  def checkReduction(op: => Expr): Expr =
    val saved = isReduced
    val result = op
    var red = false
    while isReduced ne saved do
      red = isReduced.head || red
      isReduced = isReduced.tail
    conclude(red)(result)

  def popLastReduction(): Boolean =
    val res = isReduced.head
    isReduced = isReduced.tail
    res

  override def mapValRef(e: ValRef): Expr =
    e.sym match
      case sym @ ParamSymbol(_, _) =>
        nonReduced(e)
      case sym @ ValDefSymbol(_) =>
        val result = this(sym.dealias.expr)
        result

  override def mapPiType(e: PiType): Expr = checkReduction {
    super.mapPiType(e)
  }

  override def mapPiTypeParamRef(e: PiTypeParamRef): Expr =
    nonReduced(super.mapPiTypeParamRef(e))

  override def mapPiIntro(e: PiIntro): Expr = checkReduction {
    super.mapPiIntro(e)
  }

  override def mapPiIntroParamRef(e: PiIntroParamRef): Expr =
    nonReduced(super.mapPiIntroParamRef(e))

  override def mapPiElim(e: PiElim): Expr =
    val e0 @ PiElim(fun1, arg1) = checkReduction(super.mapPiElim(e))
    val red = popLastReduction()
    fun1 match
      case fun1: PiIntro =>
        val body = Typer.substBinder(fun1, arg1, fun1.body)
        val e1 = this(body)
        val red1 = popLastReduction()
        if e1.isInstanceOf[Match] && false then
          conclude(red)(e0)
        else conclude(red1 || red)(e1)
      case _ => conclude(red)(fun1)

  override def mapAppliedDataCon(e: AppliedDataCon): Expr = checkReduction {
    super.mapAppliedDataCon(e)
  }

  override def mapAppliedTypeCon(e: AppliedTypeCon): Expr = checkReduction {
    super.mapAppliedTypeCon(e)
  }

  override def mapMatch(e: Match): Expr = {
    val scrut = this(e.scrutinee)
    popLastReduction()
    if Reducer.isNeutralExpr(scrut) then
      nonReduced(e)
    else
      scrut match
        case AppliedDataCon(dconSym, args) =>
          @annotation.tailrec def recur(cdefs: List[CaseDef]): Expr =
            cdefs match
              case Nil => assert(false)
              case (binder @ CaseDef(pat, body)) :: cdefs =>
                if pat.datacon.name == dconSym.name then
                  val substitutor = new ExprMap:
                    override def mapPatternBoundParamRef(e: PatternBoundParamRef): Expr =
                      if e.binder.exprId == binder.exprId then
                        args(e.paramIdx)
                      else
                        super.mapPatternBoundParamRef(e)
                  val body1 = substitutor(body)
                  val body2 = checkReduction(this(body1))
                  popLastReduction()
                  reduced(body2)
                else recur(cdefs)
          recur(e.cases)
        case _ => assert(false)
  }

  override def mapPatternBoundParamRef(e: PatternBoundParamRef): Expr =
    nonReduced(super.mapPatternBoundParamRef(e))

  override def mapType(tp: Type): Expr =
    checkReduction(Type(this(tp.level)))

  override def mapLevel(e: Level): Expr =
    nonReduced(e)

  override def mapLZero(e: LZero): Expr =
    nonReduced(e)

  override def mapLSucc(e: LSucc): Expr =
    LSucc(this(e.pred))

  protected def reduceLLub(e: LLub): Expr =
    var reduced: Boolean = false
    @annotation.tailrec def reconSuc(l: Expr, suc: Int): Expr =
      if suc <= 0 then l
      else reconSuc(LSucc(l), suc - 1)
    @annotation.tailrec def recur(l1: Expr, l2: Expr, suc: Int): Expr =
      (l1, l2) match
        case (LSucc(l1), LSucc(l2)) =>
          reduced = true
          recur(l1, l2, suc + 1)
        case (LZero(), l2) =>
          reduced = true
          reconSuc(l2, suc)
        case (l1, LZero()) =>
          reduced = true
          reconSuc(l1, suc)
        case (l1, l2) =>
          reduced = true
          reconSuc(LLub(l1, l2), suc)
    val result = recur(e.l1, e.l2, 0)
    conclude(reduced)(result)

  override def mapLLub(e: LLub): Expr =
    val res = checkReduction(super.mapLLub(e))
    val red = popLastReduction()
    val res1 = reduceLLub(res.asInstanceOf)
    val red1 = popLastReduction()
    conclude(red || red1)(res1)

  override def apply(e: Expr): Expr =
    val prevLen = isReduced.length
    val result = trace(s"reduce ${e.show}", showOp = (x: Expr) => x.show) { super.apply(e) }
    val nowLen = isReduced.length
    assert(nowLen == prevLen + 1, s"isReduced stack $prevLen --> $nowLen for $e --> $result")
    result

object Reducer:
  def isNeutralExpr(e: Expr): Boolean = e match
    case ValRef(sym) => sym match
      case ParamSymbol(myName, myInfo) => true
      case ValDefSymbol(myName) => false
    case PiTypeParamRef() => true
    case PiIntroParamRef() => true
    case PiElim(func, arg) =>
      isNeutralExpr(func)
    case Match(scrutinee) =>
      isNeutralExpr(scrutinee)
    case PatternBoundParamRef(paramIdx) =>
      true
    case _ => false

  def reduce(e: Expr): Expr =
    val reducer = new Reducer
    reducer(e)
