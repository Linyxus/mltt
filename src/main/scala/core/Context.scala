package core

class Context:
  import Context._
  import DataInfo._
  import ast._
  import TypedExprs.ValRef
  import core.Symbols._
  import evaluator.{EvalContext, Evaluator, Value}
  import Value._

  private var dataInfos: List[TypeConInfo] = List.empty

  private var valInfos: List[ValInfo] = List.empty

  private var bindings: Map[String, ValSymbol] = Map.empty

  def fresh: Context =
    val freshCtx = new Context
    freshCtx.dataInfos = dataInfos
    freshCtx.valInfos = valInfos
    freshCtx.bindings = bindings
    freshCtx

  def toEvalContext: EvalContext =
    val ectx = new EvalContext
    for info <- valInfos.reverse do
      Evaluator.evalDef(info.sym, info.expr)(using ectx)
    bindings.foreach((_, sym) => ectx.addBinding(sym, NeutralValue(Neutral.Var(sym)).withType(sym.info)))
    ectx

  def description(showOp: TypedExprs.Expr => String): String =
    val sb = StringBuilder()
    bindings.foreach { (_, sym) =>
      sb ++= s"${sym.name} : ${showOp(sym.info)}\n"
    }
    sb.result

  def withBinding[T](sym: ValSymbol)(op: Context ?=> T): T =
    val freshCtx = fresh
    freshCtx.bindings = bindings + (sym.name -> sym)
    op(using freshCtx)

  def withDataInfo[T](info: TypeConInfo)(op: Context ?=> T): T =
    val freshCtx = fresh
    freshCtx.addDataInfo(info)
    op(using freshCtx)

  def withValInfo[T](info: ValInfo)(op: Context ?=> T): T =
    val freshCtx = fresh
    freshCtx.addValInfo(info)
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

