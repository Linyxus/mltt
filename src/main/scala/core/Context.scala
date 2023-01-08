package core

import Context._
import DataInfo._
import ast.{TypedExprs => tpd, _}
import core._
import core.Symbols._
import core.messages._
import evaluator.{EvalContext, Evaluator, Value}
import Value._
import utils.SrcPosPrinter

class Context:

  private var dataInfos: List[TypeConInfo] = List.empty
  private var valInfos: List[ValInfo] = List.empty
  private var bindings: Map[String, ValSymbol] = Map.empty
  private var myConstr: EqConstraint = EqConstraint.empty
  private var localSyms: Set[ValDefSymbol] = Set.empty
  private var currentUVarScope: UVarScope = new UVarScope(null)
  private var freshCounter: Int = 0
  private var mySource: String | Null = null
  private var mySrcPosPrinter: SrcPosPrinter | Null = null
  private var messageLogger = MessageLogger()

  def fresh: Context =
    val freshCtx = new Context
    freshCtx.dataInfos = dataInfos
    freshCtx.valInfos = valInfos
    freshCtx.bindings = bindings
    freshCtx.myConstr = myConstr
    freshCtx.localSyms = localSyms
    freshCtx.currentUVarScope = currentUVarScope
    freshCtx.freshCounter = freshCounter
    freshCtx.mySource = mySource
    freshCtx.mySrcPosPrinter = mySrcPosPrinter
    freshCtx.messageLogger = messageLogger
    freshCtx

  def report(msg: Message): Unit = messageLogger.log(msg)

  def messages: List[Message] = messageLogger.messages.reverse

  def currentSource: String = mySource

  def setSource(source: String): this.type =
    mySource = source
    this

  def setupSrcPosPrinter: this.type =
    mySrcPosPrinter = new SrcPosPrinter:
      val source = mySource
    this

  def showSrcPos(srcPos: SrcPos, hint: Option[String]): String =
    assert(mySrcPosPrinter ne null)
    mySrcPosPrinter.nn.showSrcPos(srcPos, hint)

  def freshen(x: String): String =
    freshCounter += 1
    x + "$" + freshCounter.toString

  def trackUVarInfo(info: UVarInfo): Unit =
    currentUVarScope.track(info)

  def uvarScope: UVarScope = currentUVarScope
  def enterUVarScope: Unit = currentUVarScope = UVarScope(currentUVarScope)
  def rollbackUVarScope: Unit = currentUVarScope = currentUVarScope.parent

  def constraint: EqConstraint = myConstr

  def constraint_=(newConstr: EqConstraint): Unit = myConstr = newConstr

  def toEvalContext: EvalContext =
    val ectx = new EvalContext
    for info <- valInfos.reverse do
      Evaluator.evalDef(info.sym, info.expr.get)(using ectx)
    bindings.foreach((_, sym) => ectx.addBinding(sym, NeutralValue(Neutral.Var(sym)).withType(sym.info)))
    ectx

  def description(showOp: tpd.Expr => String): String =
    val sb = StringBuilder()
    bindings.foreach { (_, sym) =>
      sb ++= s"${sym.name} : ${showOp(sym.info)}\n"
    }
    localSyms.foreach { sym =>
      val vinfo = lookupValDef(sym.name).get
      sb ++= s"${sym.name} : ${showOp(vinfo.info)}\n"
    }
    sb.result

  def withBinding[T](sym: ValSymbol)(op: Context ?=> T): T =
    val freshCtx = fresh
    freshCtx.bindings = bindings + (sym.name -> sym)
    op(using freshCtx)

  def withBindings[T](syms: List[ValSymbol])(op: Context ?=> T): T =
    val freshCtx = fresh
    freshCtx.bindings = bindings ++ (syms.map(sym => sym.name -> sym))
    op(using freshCtx)

  def withDataInfo[T](info: TypeConInfo)(op: Context ?=> T): T =
    val freshCtx = fresh
    freshCtx.addDataInfo(info)
    op(using freshCtx)

  def withValInfo[T](info: ValInfo, local: Boolean = false)(op: Context ?=> T): T =
    val freshCtx = fresh
    freshCtx.addValInfo(info)
    if local then freshCtx.localSyms += info.sym
    op(using freshCtx)

  def addDataInfo(info: TypeConInfo): Unit =
    dataInfos = info :: dataInfos

  def addValInfo(info: ValInfo): Unit =
    valInfos = info :: valInfos

  def lookupBindings(name: String): Option[ValSymbol] = bindings.get(name)

  def lookupTypeConInfo(name: String): Option[TypeConInfo] =
    @scala.annotation.tailrec
    def recur(infos: List[TypeConInfo]): Option[TypeConInfo] = infos match
      case Nil => None
      case info :: infos =>
        if info.name == name then Some(info) else recur(infos)
    recur(dataInfos)

  def lookupDataConInfo(name: String, expectedTypeCon: Option[String]): Option[DataConInfo] =
    def lookupIn(tyConInfo: TypeConInfo): Option[DataConInfo] =
      @scala.annotation.tailrec
      def recur(xs: List[DataConInfo]): Option[DataConInfo] = xs match
        case Nil => None
        case x :: xs => if x.name == name then Some(x) else recur(xs)
      recur(tyConInfo.constructors)
    expectedTypeCon match
      case None =>
        @scala.annotation.tailrec
        def recur(xs: List[TypeConInfo]): Option[DataConInfo] = xs match
          case Nil => None
          case x :: xs => lookupIn(x) match
            case None => recur(xs)
            case Some(info) => Some(info)
        recur(dataInfos)
      case Some(tyconName) => lookupTypeConInfo(tyconName).flatMap(lookupIn)

  def lookupValDef(name: String): Option[ValDefSymbol] =
    @annotation.tailrec def recur(xs: List[ValInfo]): Option[ValDefSymbol] =
      xs match
        case x :: xs => if x.sym.name == name then Some(x.sym) else recur(xs)
        case Nil => None
    recur(valInfos)

  def lookupVal(name: String): Option[ValSymbol] =
    lookupBindings(name).orElse(lookupValDef(name))

  def lookup(name: String): Option[VarInfo] =
    lookupTypeConInfo(name) orElse lookupDataConInfo(name, None) orElse lookupVal(name)

object Context:
  import ast._
  import DataInfo._
  import core.Symbols._

  type DefInfo = ValInfo | DataInfo

  type VarInfo = DataInfo | Symbol
  def apply(): Context = new Context

  def ctx(using Context): Context = summon[Context]

