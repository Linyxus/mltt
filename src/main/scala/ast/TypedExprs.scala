package ast

import core.Symbols._
import ast.Level

object TypedExprs {
  sealed trait Expr {
    private var myTpe: Expr | Null = null
    def tpe: Expr =
      assert(myTpe ne null, toString)
      myTpe.nn

    def withType(tp: Expr): this.type =
      withTypeUnchecked(tp)

    def withTypeUnchecked(tp: Expr): this.type =
      myTpe = tp
      this

    def show: String
  }

  trait ParamRef {
    type BinderType <: PiType | PiIntro | CaseDef
    private var myBinder: BinderType | Null = null
    def binder: BinderType =
      assert(myBinder ne null, this)
      myBinder.nn
    def hasBinder: Boolean = myBinder ne null
    def overwriteBinder(newBinder: BinderType): this.type =
      myBinder = newBinder
      this
  }

  case class ValRef(sym: ValSymbol) extends Expr {
    override def tpe: Expr = sym.info
    override def withType(tp: Expr): this.type =
      assert(false)
      this
    override def toString(): String = s"ValRef(${sym.name})"

    def show: String = sym.name
  }

  case class PiType(argName: String, argTyp: Expr, resTyp: Expr) extends Expr {
    def computeType: Type =
      (argTyp.tpe, resTyp.tpe) match
        case (Type(l1), Type(l2)) => Type(l1 lub l2)
        case _ => assert(false)

    def withType(): this.type = withType(computeType)

    override def toString(): String = s"PiType@${hashCode()}($argName, $argTyp, $resTyp)"

    def show: String = s"(($argName: ${argTyp.show}) -> ${resTyp.show})"
  }
  case class PiTypeParamRef() extends Expr with ParamRef {
    type BinderType = PiType
    override def tpe: Expr = binder.argTyp
    override def withType(tp: Expr): this.type = assert(false)

    override def toString(): String =
      if hasBinder then
        // binder.argName
        s"<${binder.hashCode()}:${binder.argName}>"
      else
        "<unbound:∀>"

    def show: String = binder.argName
  }

  case class PiIntro(argName: String, argTyp: Expr) extends Expr {
    private var myBody: Expr | Null = null
    def body: Expr = myBody.nn
    def withBody(e: Expr): this.type =
      myBody = e
      this

    override def toString(): String = s"PiIntro@${hashCode()}($argName, $argTyp, $body)"

    def show: String = s"(($argName:${argTyp.show}) => ${body.show})"
  }
  case class PiIntroParamRef() extends Expr with ParamRef {
    type BinderType = PiIntro
    override def tpe: Expr = binder.argTyp
    override def withType(tp: Expr): this.type = assert(false)

    override def toString(): String =
      if hasBinder then
        s"<${binder.hashCode()}:${binder.argName}>"
      else
        "<unbound:λ>"

    def show: String = binder.argName
  }

  case class PiElim(func: Expr, arg: Expr) extends Expr {
    def show: String = s"(${func.show} ${arg.show})"
  }

  case class AppliedTypeCon(tycon: TypeConSymbol, args: List[Expr]) extends Expr {
    def show: String = s"${tycon.name}(${args.map(_.show).mkString(", ")})"
  }
  case class AppliedDataCon(datacon: DataConSymbol, args: List[Expr]) extends Expr {
    def show: String = s"${datacon.name}(${args.map(_.show).mkString(", ")})"
  }

  case class Pattern(datacon: DataConSymbol, args: List[String])
  case class CaseDef(pat: Pattern, body: Expr) {
    private var myPatMat: Match | Null = null
    def patmat: Match = myPatMat.nn
    def overwritePatMat(patmat: Match): this.type =
      myPatMat = patmat
      this
  }
  case class Match(scrutinee: Expr, cases0: Match => List[CaseDef]) extends Expr {
    val cases: List[CaseDef] = cases0(this)

    override def toString(): String = s"Match($scrutinee, $cases)"
    def show: String = "MATCH"
  }

  case class PatternBoundParamRef(paramIdx: Int) extends Expr with ParamRef {
    type BinderType = CaseDef
    override def tpe: Expr =
      binder.pat.datacon.info.paramTypeOf(paramIdx)
    override def withType(tp: Expr): this.type = assert(false)

    override def toString(): String =
      if hasBinder then
        binder.pat.args(paramIdx)
      else "<unbound:pattern>"

     def show: String = binder.pat.args(paramIdx)
  }
  case class Type(level: Level) extends Expr {
    override def tpe: Expr =
      Type(Level.LSucc(level))
    override def withType(tp: Expr): this.type = assert(false)

    def show: String = "Type"
  }

  case class Wildcard() extends Expr {
    def show: String = "_"
  }

  trait ExprTraverser:
    def traverseSubtrees(e: Expr): Unit =
      if !e.isInstanceOf[Type] then
        e match
          case e: ParamRef =>
            if e.hasBinder then traverse(e.tpe)
          case _ =>
            traverse(e.tpe)
      e match
        case ValRef(sym) => ()
        case PiType(argName, argTyp, resTyp) =>
          traverse(argTyp)
          traverse(resTyp)
        case PiTypeParamRef() => ()
        case PiIntro(argName, argTyp) => traverse(argTyp)
        case PiIntroParamRef() => ()
        case PiElim(func, arg) =>
          traverse(func)
          traverse(arg)
        case AppliedTypeCon(tycon, args) =>
          args.foreach(traverse)
        case AppliedDataCon(datacon, args) =>
          args.foreach(traverse)
        case e @ Match(scrutinee, _) =>
          traverse(scrutinee)
          e.cases.foreach { case CaseDef(_, body) =>
            traverse(body)
          }
        case PatternBoundParamRef(paramIdx) => ()
        case Type(level) => ()
        case Wildcard() => ()

    def traverseValRef(e: ValRef): Unit =
      traverseSubtrees(e)

    def traversePiType(e: PiType): Unit = traverseSubtrees(e)

    def traversePiTypeParamRef(e: PiTypeParamRef): Unit = traverseSubtrees(e)

    def traversePiIntro(e: PiIntro): Unit = traverseSubtrees(e)

    def traversePiIntroParamRef(e: PiIntroParamRef): Unit = traverseSubtrees(e)

    def traversePiElim(e: PiElim): Unit = traverseSubtrees(e)

    def traverseAppliedTypeCon(e: AppliedTypeCon): Unit = traverseSubtrees(e)

    def traverseAppliedDataCon(e: AppliedDataCon): Unit = traverseSubtrees(e)

    def traverseMatch(e: Match): Unit = traverseSubtrees(e)

    def traversePatternBoundParamRef(e: PatternBoundParamRef): Unit =
      traverseSubtrees(e)

    def traverseType(e: Type): Unit =
      traverseSubtrees(e)

    def traverseWildcard(e: Wildcard): Unit =
      traverseSubtrees(e)

    def traverse(e: Expr): Unit = e match
      case e @ ValRef(sym) => traverseValRef(e)
      case e @ PiType(argName, argTyp, resTyp) => traversePiType(e)
      case e @ PiTypeParamRef() => traversePiTypeParamRef(e)
      case e @ PiIntro(argName, argTyp) => traversePiIntro(e)
      case e @ PiIntroParamRef() => traversePiIntroParamRef(e)
      case e @ PiElim(func, arg) => traversePiElim(e)
      case e @ AppliedTypeCon(tycon, args) => traverseAppliedTypeCon(e)
      case e @ AppliedDataCon(datacon, args) => traverseAppliedDataCon(e)
      case e @ Match(scrutinee, cases0) => traverseMatch(e)
      case e @ PatternBoundParamRef(paramIdx) => traversePatternBoundParamRef(e)
      case e @ Type(level) => traverseType(e)
      case e @ Wildcard() => traverseWildcard(e)

  trait ExprMap:
    def isDebugging: Boolean = false

    private def updatePiTypeParamRef(old: PiType, neo: PiType, e: Expr): Unit =
      val traverser = new ExprTraverser:
        override def traversePiTypeParamRef(e: PiTypeParamRef): Unit =
          if e.hasBinder && (e.binder eq old) then e.overwriteBinder(neo)
          traverseSubtrees(e)
      traverser.traverse(e)

    private def updatePiIntroParamRef(old: PiIntro, neo: PiIntro, e: Expr): Unit =
      val traverser = new ExprTraverser:
        override def traversePiIntroParamRef(e: PiIntroParamRef): Unit =
          if e.hasBinder && (e.binder eq old) then e.overwriteBinder(neo)
          traverseSubtrees(e)

    def mapValRef(e: ValRef): Expr = e

    def mapPiType(e: PiType): Expr =
      val res = PiType(e.argName, this(e.argTyp), this(e.resTyp)).withType(this(e.tpe))
      updatePiTypeParamRef(e, res, res.resTyp)
      res

    def mapPiTypeParamRef(e: PiTypeParamRef): Expr = e

    def mapPiIntro(e: PiIntro): Expr =
      val res = PiIntro(e.argName, this(e.argTyp)).withBody(this(e.body)).withType(this(e.tpe))
      updatePiIntroParamRef(e, res, res.body)
      res

    def mapPiIntroParamRef(e: PiIntroParamRef): Expr = e

    def mapPiElim(e: PiElim): Expr =
      PiElim(this(e.func), this(e.arg)).withType(this(e.tpe))

    def mapAppliedTypeCon(e: AppliedTypeCon): Expr =
      AppliedTypeCon(e.tycon, e.args.map(this.apply(_))).withType(this(e.tpe))

    def mapAppliedDataCon(e: AppliedDataCon): Expr =
      AppliedDataCon(e.datacon, e.args.map(this(_))).withType(this(e.tpe))

    def mapCaseDef(pm: Match, cdef: CaseDef): CaseDef =
      CaseDef(cdef.pat, this(cdef.body)).overwritePatMat(pm)

    def mapMatch(e: Match): Expr =
      val res = Match(this(e.scrutinee), patmat => e.cases.map(mapCaseDef(patmat, _)))
      res.withType(this(e.tpe))

    def mapPatternBoundParamRef(e: PatternBoundParamRef): Expr =
      e

    def mapType(e: Type): Expr = e

    def mapWildcard(e: Wildcard): Expr = e.withType(this(e.tpe))

    def apply(t: Expr): Expr =
      val result = t match
        case e @ ValRef(sym) => mapValRef(e)
        case e @ PiType(argName, argTyp, resTyp) =>
          mapPiType(e)
        case e @ PiTypeParamRef() =>
          mapPiTypeParamRef(e)
        case e @ PiIntro(argName, argTyp) => mapPiIntro(e)
        case e @ PiIntroParamRef() => mapPiIntroParamRef(e)
        case e @ PiElim(func, arg) => mapPiElim(e)
        case e @ AppliedTypeCon(tycon, args) => mapAppliedTypeCon(e)
        case e @ AppliedDataCon(datacon, args) => mapAppliedDataCon(e)
        case e @ Match(scrutinee, cases0) => mapMatch(e)
        case e @ PatternBoundParamRef(paramIdx) => mapPatternBoundParamRef(e)
        case e @ Type(level) => mapType(e)
        case e @ Wildcard() => mapWildcard(e)
      if isDebugging then
        println(s"ExprMap: map $t --> $result")
      result
}

