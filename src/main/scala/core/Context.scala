package core

class Context:
  import Context._
  import DataInfo._
  import ast._
  import core.Symbols._

  private var dataInfos: List[TypeConInfo] = List.empty

  private var bindings: Map[String, ValSymbol] = Map.empty

  def fresh: Context =
    val freshCtx = new Context
    freshCtx.dataInfos = dataInfos
    freshCtx.bindings = bindings
    freshCtx

  def withBinding[T](sym: ValSymbol)(op: Context ?=> T): T =
    val freshCtx = fresh
    freshCtx.bindings = bindings + (sym.name -> sym)
    op(using freshCtx)

  def withDataInfo[T](info: TypeConInfo)(op: Context ?=> T): T =
    val freshCtx = fresh
    freshCtx.dataInfos = info :: dataInfos
    op(using freshCtx)

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

  def lookup(name: String): Option[VarInfo] =
    lookupTypeConInfo(name) orElse lookupDataConInfo(name, None) orElse lookupBindings(name)

object Context:
  import ast._
  import DataInfo._
  import core.Symbols._

  type VarInfo = DataInfo | Symbol
  def apply(): Context = new Context

  def ctx(using Context): Context = summon[Context]

