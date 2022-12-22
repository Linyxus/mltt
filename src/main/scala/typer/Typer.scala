package  typer

import core._
import ast._

class Typer:
  import Typer._
  import DataInfo._
  import Context._

  def isUniverse(e: Expr)(using Context): TyperResult[Unit] = e match
    case _: Type => Right(())
    case Wildcard => Right(())
    case _ => Left(s"not supported: isType($e)")

  def typedDataDef(dataDef: DataDef)(using Context): TyperResult[TypeConInfo] =
    def checkTypeConSig(sig: Expr): TyperResult[Unit] = sig match
      case Type(l) => Right(())
      case Pi(argName, argTyp, resTyp) => checkTypeConSig(resTyp)
      case _ => Left(s"invalid datadef signature: ${dataDef.sig}")

    def checkDataConSig(sig: Expr): TyperResult[Unit] = sig match
      case ApplyTypeCon(name, _) if name == dataDef.name => Right(())
      case Pi(_, _, resTyp) => checkDataConSig(resTyp)
      case _ => Left(s"invalid data constructor signature: $sig")

    def typedDataCon(consDef: ConsDef): TyperResult[TypeConInfo => DataConInfo] =
      val dummy = TypeConInfo(dataDef.name, ???, _ => Nil)
      ctx.withDataInfo(dummy) {
        checkDataConSig(consDef.sig).flatMap { _ =>
          typed(consDef.sig).map(_ => (info: TypeConInfo) => DataConInfo(consDef.name, info, ???))
        }
      }

    checkTypeConSig(dataDef.sig).flatMap { _ =>
      typed(dataDef.sig).flatMap { _ =>
        val dataconsM: List[TyperResult[TypeConInfo => DataConInfo]] = dataDef.constructors.map(typedDataCon(_))
        collectAll(dataconsM) map { datacons =>
          TypeConInfo(dataDef.name, ???, (info: TypeConInfo) => datacons.map(f => f(info)))
        }
      }
    }

  def isMatchingTypes(tp: Expr, pt: Expr)(using Context): TyperResult[Unit] =
    // isUniverse(tp) flatMap { _ =>
    //   isUniverse(pt) flatMap { _ =>
        pt match {
          case Wildcard => Right(())
          case pt => if pt == tp then Right(()) else Left(s"type mismatch: $tp and $pt")
        }
    //   }
    // }

  def substBinder(name: String, to: Expr, expr: Expr)(using Context): Expr =
    def k(expr: Expr): Expr = substBinder(name, to, expr)
    expr match
      case Var(name1) => if name1 == name then to else Var(name1)
      case Pi(arg, typ, resTyp) => if arg == name then expr else Pi(arg, k(typ), k(resTyp))
      case PiIntro(arg, body) => if arg == name then expr else PiIntro(arg, k(body))
      case Apply(func, args) => Apply(k(func), args.map(k))
      case ApplyTypeCon(name, args) => ApplyTypeCon(name, args.map(k))
      case ApplyDataCon(name, args) => ApplyDataCon(name, args.map(k))
      case Match(scrutinee, cases) => Match(k(scrutinee), cases.map { case CaseDef(pat, body) => CaseDef(k(pat).asInstanceOf, k(body)) })
      case Type(level) => expr
      case Wildcard => Wildcard

  def typed(e: Expr, pt: Expr = Wildcard)(using Context): TyperResult[Expr] =
    typed1(e, pt) flatMap { tpe => isMatchingTypes(tpe, pt).map(_ => tpe) }

  def typed1(e: Expr, pt: Expr = Wildcard)(using Context): TyperResult[Expr] = e match
    case Var(name) => ctx.lookupBindings(name) match {
      case Some(expr) => isMatchingTypes(expr, pt).map(_ => expr)
      case None => Left(s"unknown variable $name")
    }
    case Apply(expr, args) => typedApply(expr, args)
    case ApplyTypeCon(name, args) =>
      ctx.lookupTypeConInfo(name) match
        case None => Left(s"unknown type constructor $name")
        case Some(tycon) => typedApplyTypeCon(tycon, args)
    case ApplyDataCon(name, args) =>
      def getExpectedTypeCon: Option[String] =
        pt match
          case ApplyTypeCon(name, _) => Some(name)
          case _ => None

      ctx.lookupDataConInfo(name, getExpectedTypeCon) match
        case None => Left(s"unknown data constructor $name")
        case Some(con) => typedApplyDataCon(con, args)
    case Pi(arg, typ, resTyp) =>
      typed(typ) flatMap {
        case Type(lTyp) =>
          ctx.withBinding(arg, typ) {
            typed(resTyp) flatMap {
              case Type(lRes) =>
                Right(Type(lTyp lub lRes))
              case _ =>
                Left(s"return type $typ is not a type")
            }
          }
        case _ => Left(s"cannot abstract over $typ")
      }
    case PiIntro(argName, body) => typedPiIntro(argName, body, pt)
    case Type(l) => Right(Type(Level.LSucc(l)))
    case _ => Left(s"not supported: typed($e)")

  def typedPiIntro(argName: String, body: Expr, pt: Expr)(using Context): TyperResult[Expr] =
    pt match
      case Pi(eargName, eargTyp, eresTyp) =>
        typed(eargTyp).flatMap { tpe =>
          isUniverse(tpe) flatMap { _ =>
            ctx.withBinding(eargName, eargTyp)(typed(substBinder(argName, Var(eargName), body), eresTyp).map(Pi(eargName, eargTyp, _)))
          }
        }
      case _ => Left(s"cannot type function with expected type $pt")

  def collectAll[X](xs: List[TyperResult[X]]): TyperResult[List[X]] = xs match
    case Nil => Right(Nil)
    case x :: xs => x.flatMap(x => collectAll(xs).map(x :: _))

  def typedArgs(actual: List[Expr], expected: List[Expr])(using Context): TyperResult[Unit] =
    if actual.length != expected.length then Left(s"number of argument mismatch")
    else
      def resArgs: List[TyperResult[Expr]] = actual.zip(expected).map((a, e) => typed(a, e))
      collectAll(resArgs).map(_ => ())

  def typedApplyTypeCon(info: TypeConInfo, args: List[Expr])(using Context): TyperResult[Expr] =
    typedApplyFunctionParams(???, args)

  def typedApplyDataCon(info: DataConInfo, args: List[Expr])(using Context): TyperResult[Expr] =
    typedApplyFunctionParams(???, args)

  def typedApplyFunction(funType: Expr, arg: Expr)(using Context): TyperResult[Expr] =
    funType match
      case Pi(argName, typ, resTyp) =>
        typed(arg, typ) map { _ => substBinder(argName, arg, resTyp) }
      case _ => Left(s"cannot apply value of type $funType")

  def typedApplyFunctionParams(funType: Expr, arg: List[Expr])(using Context): TyperResult[Expr] =
    def recur(xs: List[Expr], acc: TyperResult[Expr]): TyperResult[Expr] = xs match
      case Nil => acc
      case x :: xs => recur(xs, acc.flatMap(typedApplyFunction(_, x)))
    recur(arg, Right(funType))

  def typedApply(fun: Expr, args: List[Expr])(using Context): TyperResult[Expr] =
    fun match
      case Var(funcName) =>
        ctx.lookup(funcName) match
          case None => Left(s"unknown name: $funcName when typing apply")
          case Some(info) => info match
            case info: TypeConInfo => typedApplyTypeCon(info, args)
            case info: DataConInfo => typedApplyDataCon(info, args)
            case typ: Expr => typedApplyFunctionParams(typ, args)
            case _ => Left(s"not supported: $info as the function in typedApply")
      case _ => Left(s"not supported: applying $fun")


object Typer:
  type TyperResult[+X] = Either[String, X]

