package parser

import ast._
import ast.{Commands => cmd}
import scala.annotation.tailrec

class Parser(source: String):
  import Parser._

  private var tokens: LazyList[Token] = Tokenizer.getTokensLazy(source)
  tokens.toList
  private def current = tokens.head
  private var indentLevel: Int = 0

  def peekType: TokenType = current.tp
  def step(): Unit =
    // println(s"!!! step is called")
    // assert(tokens.toList.length != 15)
    if peekType == Indent() then
      indentLevel += 1
    else if peekType == Outdent() then
      indentLevel -= 1
    tokens = tokens.tail

  def lookAheadWith(tp: TokenType): ParseResult[Token] =
    if eof then Left(s"expecting $tp but found end-of-file")
    else
      if tokens.tail.head.tp == tp then Right(tokens.tail.head)
      else Left(s"expecting $tp but found ${tokens.tail.head.tp}")

  def eof: Boolean = peekType == EOF()

  def expect(tpe: TokenType): ParseResult[Token] =
    if peekType == tpe then
      Right(current)
    else
      // assert(tpe != RightParen())
      Left(s"expecting $tpe, but found $peekType (${tokens.toList})")

  def matchAhead(tpe: TokenType): ParseResult[Token] =
    // tpe match
    //   case NewLine() =>
    //     step()
    //     matchAhead(tpe)
    //   case Outdent() =>
    //     step()
    //     matchAhead(tpe)
    //   case Indent() =>
    //     step()
    //     matchAhead(tpe)
    //   case _ =>
    expect(tpe).map(x => { step(); x })

  def parseIdentifier: ParseResult[Token] =
    peekType match
      case Ident(name) => Right(current)
      case _ => Left(s"expecting identifier, but see $peekType")

  def parsePiIntro(argName: String): ParseResult[Expr] =
    matchAhead(DoubleArrow()) flatMap { _ =>
      parseExpr map { body => PiIntro(argName, body) }
    }

  def parsePattern: ParseResult[ApplyDataCon] =
    parseIdentifier flatMap { con =>
      step()
      parseParamListWithImplicitsOptional map { (iargs, args) =>
        ApplyDataCon(con.content, iargs.getOrElse(Nil), args.getOrElse(Nil))
      }
    }

  def parseUnit: ParseResult[Unit] =
    if peekType == LeftParen() then
      lookAheadWith(RightParen()).map { _ =>
        step()
        step()
        ()
      }
    else Left(s"expecting left paren, but found $peekType")

  def parseCaseDef: ParseResult[CaseDef] =
    matchAhead(Case()) flatMap { _ =>
      parsePattern flatMap { pat =>
        matchAhead(DoubleArrow()) flatMap { _ =>
          parseUnit match
            case Left(_) =>
              parseExpr.map(x => CaseDef(pat, Some(x)))
            case Right(_) => Right(CaseDef(pat, None))
        }
      }
    }

  def parseCaseDefs: List[CaseDef] =
    @annotation.tailrec def recur(acc: List[CaseDef]): List[CaseDef] =
      parseCaseDef match
        case Left(_) => acc.reverse
        case Right(cdef) => recur(cdef :: acc)
    recur(Nil)

  def varOrPiIntro: ParseResult[Expr] =
    parseIdentifier.flatMap {
      case Token(_, name) =>
        step()
        if peekType == DoubleArrow() then
          parsePiIntro(name)
        else
          Right(Var(name))
    }

  def parsePi: ParseResult[Expr] =
    matchAhead(LeftParen()) flatMap { _ =>
      parseIdentifier flatMap {
        case Token(_, content) =>
          step()
          matchAhead(Colon()) flatMap { _ =>
            parseExpr flatMap { argTyp =>
              matchAhead(RightParen()) flatMap { _ =>
                matchAhead(Arrow()) flatMap { _ =>
                  parseExpr map { resTyp => Pi(content, argTyp, resTyp, false) }
                } orElse {
                  matchAhead(QuestionArrow()) flatMap { _ =>
                    parseExpr map { resTyp => Pi(content, argTyp, resTyp, true) }
                  }
                }
              }
            }
          }
      }
    }

  def parseParamListWithImplicits: ParseResult[(Option[List[Expr]], Option[List[Expr]])] =
    def parseMoreParam: ParseResult[Expr] =
      matchAhead(Comma()) flatMap { _ => parseExpr }
    def parseMoreParams: List[Expr] =
      @annotation.tailrec def recur(acc: List[Expr]): List[Expr] =
        parseMoreParam match
          case Left(_) => acc.reverse
          case Right(arg) => recur(arg :: acc)
      recur(Nil)

    matchAhead(LeftParen()) flatMap { _ =>
      if peekType == RightParen() then
        step()
        Right((None, Some(Nil)))
      else
        val isImp: Boolean = peekType == Using() && { step(); true }
        val res = parseExpr flatMap { arg1 =>
          val args = arg1 :: parseMoreParams
          matchAhead(RightParen()) map { _ => args }
        }
        if isImp then
          res.flatMap { args => parseParamListOptional.map(xs => (Some(args), xs)) }
        else res.map(xs => (None, Some(xs)))
    }

  def parseParamListWithImplicitsOptional: ParseResult[(Option[List[Expr]], Option[List[Expr]])] =
    if peekType == LeftParen() then
      parseParamListWithImplicits
    else Right(None, None)

  def parseParamListOptional: ParseResult[Option[List[Expr]]] =
    if peekType == LeftParen() then parseParamList.map(Some(_)) else Right(None)

  def parseParamList: ParseResult[List[Expr]] =
    def parseMoreParam: ParseResult[Expr] =
      matchAhead(Comma()) flatMap { _ => parseExpr }
    def parseMoreParams: List[Expr] =
      @annotation.tailrec def recur(acc: List[Expr]): List[Expr] =
        parseMoreParam match
          case Left(_) => acc.reverse
          case Right(arg) => recur(arg :: acc)
      recur(Nil)
    matchAhead(LeftParen()) flatMap { _ =>
      if peekType == RightParen() then
        step()
        Right(Nil)
      else
        parseExpr flatMap { arg1 =>
          val args = arg1 :: parseMoreParams
          matchAhead(RightParen()) map { _ => args }
        }
    }

  def parseExpr: ParseResult[Expr] = parseExprAtom flatMap { e =>
    @annotation.tailrec def recur(acc: Expr): ParseResult[Expr] =
      if peekType == LeftParen() then
        parseParamListWithImplicits match
          case err @ Left(_) => err.asInstanceOf[ParseResult[Expr]]
          case Right((ips, ps)) => (ips, ps) match
            case (Some(ips), Some(ps)) =>
              recur(Apply(Apply(acc, ips, imp = true), ps, imp = false))
            case (Some(ips), None) =>
              recur(Apply(acc, ips, imp = true))
            case (None, Some(ps)) =>
              recur(Apply(acc, ps, imp = false))
            case (None, None) => assert(false)
      else if peekType == parser.Match() then
        step()
        Right(Match(acc, parseCaseDefs))
      else Right(acc)
    val result = recur(e)
    result
  }

  def parseType: ParseResult[Expr] =
    step()
    if peekType != LeftParen() then
      Right(Type(LZero()))
    else
      matchAhead(LeftParen()) flatMap { _ =>
        parseExpr flatMap { level =>
          matchAhead(RightParen()) map { _ =>
            Type(level)
          }
        }
      }
      // Right(Type(LZero()))

  def parseLSucc: ParseResult[Expr] =
    step()
    matchAhead(LeftParen()) flatMap { _ =>
      parseExpr flatMap { x =>
        matchAhead(RightParen()) map { _ => LSucc(x) }
      }
    }

  def parseLLub: ParseResult[Expr] =
    step()
    parseParamList flatMap {
      case p1 :: p2 :: Nil => Right(LLub(p1, p2))
      case _ => Left(s"`lub` has to be applied to two arguments")
    }

  def parseExprAtom: ParseResult[Expr] = peekType match
    case ThreeQuestionMarks() =>
      step()
      Right(Undefined())
    case Ident(name) if name == "Type" => parseType
    case Ident(name) if name == "Level" =>
      step()
      Right(Level())
    case Ident(name) if name == "lzero" =>
      step()
      Right(LZero())
    case Ident(name) if name == "lsuc" => parseLSucc
    case Ident(name) if name == "lub" => parseLLub
    case Ident(name) => varOrPiIntro
    case LeftParen() => parsePi
    case LeftBrace() => parseBlock
    case ErrorToken(msg) => Left(s"tokeniaztion error: $msg")
    case _ => Left(s"unexpected token type $peekType, (${tokens.toList})")

  def parseMany[T](lead: TokenType, op: () => ParseResult[T]): ParseResult[List[T]] =
    @annotation.tailrec def recur(acc: List[T]): ParseResult[List[T]] =
      if lead == peekType then
        op() match
          case Left(err) => Left(err)
          case Right(x) => recur(x :: acc)
      else Right(acc.reverse)
    recur(Nil)

  def parseFormal: ParseResult[(String, Expr)] =
    parseIdentifier flatMap { case Token(_, argName) =>
      step()
      matchAhead(Colon()) flatMap { _ =>
        parseExpr.map(argTyp => (argName, argTyp))
      }
    }

  def parseFormalListWithImplicits: ParseResult[(List[(String, Expr)], List[(String, Expr)])] =
    matchAhead(LeftParen()) flatMap { _ =>
      if peekType == RightParen() then
        step()
        Right((Nil, Nil))
      else
        val isImp =
          if peekType == Using() then
            step()
            true
          else false
        val result = parseFormal flatMap { arg1 =>
          def parseMoreFormal: ParseResult[(String, Expr)] =
            matchAhead(Comma()) flatMap { _ => parseFormal }
          parseMany(Comma(), () => parseMoreFormal) flatMap { args => matchAhead(RightParen()).map(_ => arg1 :: args) }
        }
        if isImp then
          result flatMap { imps => parseFormalListOptional.map(args => (imps, args)) }
        else result.map(x => (Nil, x))
    }

  def parseFormalList: ParseResult[List[(String, Expr)]] =
    matchAhead(LeftParen()) flatMap { _ =>
      if peekType == RightParen() then
        step()
        Right(Nil)
      else
        parseFormal flatMap { arg1 =>
          def parseMoreFormal: ParseResult[(String, Expr)] =
            matchAhead(Comma()) flatMap { _ => parseFormal }
          parseMany(Comma(), () => parseMoreFormal) flatMap { args => matchAhead(RightParen()).map(_ => arg1 :: args) }
        }
    }

  def makePiType(args: List[(String, Expr)], resTyp: Expr, isImp: Boolean = false): Expr =
    @annotation.tailrec def recur(xs: List[(String, Expr)], acc: Expr): Expr =
      xs match
        case Nil => acc
        case (argName, argTyp) :: xs => recur(xs, Pi(argName, argTyp, acc, isImp))
    recur(args.reverse, resTyp)

  def parseDataCon: ParseResult[ConsDef] =
    matchAhead(Case()) flatMap { _ =>
      parseIdentifier flatMap { case Token(_, name) =>
        step()
        parseFormalListWithImplicitsOptional flatMap { (iformals, formals) =>
          matchAhead(Extends()) flatMap { _ =>
            parseExpr map { resTyp =>
              val sig = makePiType(iformals, makePiType(formals, resTyp), isImp = true)
              ConsDef(name, sig)
            }
          }
        }
      }
    }

  def parseFormalListOptional: ParseResult[List[(String, Expr)]] =
    if peekType == LeftParen() then
      parseFormalList
    else Right(Nil)

  def parseFormalListWithImplicitsOptional: ParseResult[(List[(String, Expr)], List[(String, Expr)])] =
    if peekType == LeftParen() then
      parseFormalListWithImplicits
    else Right((Nil, Nil))

  def parseDataDef: ParseResult[DataDef] =
    matchAhead(Enum()) flatMap { _ =>
      parseIdentifier flatMap { case Token(_, name) =>
        step()
        parseFormalListWithImplicitsOptional flatMap { (iformals, formals) =>
          matchAhead(Extends()) flatMap { _ =>
            parseExpr flatMap { resTyp =>
              val sig0 = makePiType(formals, resTyp)
              val sig = makePiType(iformals, sig0, isImp = true)
              matchAhead(Colon()) flatMap { _ =>
                parseMany(Case(), () => parseDataCon) map { conss =>
                  DataDef(name, sig, conss)
                }
              }
            }
          }
        }
      }
    }

  def makePiIntro(args: List[String], body: Expr): Expr =
    @annotation.tailrec def recur(xs: List[String], acc: Expr): Expr =
      xs match
        case Nil => acc
        case x :: xs => recur(xs, PiIntro(x, acc))
    recur(args.reverse, body)

  def parseBlock: ParseResult[Expr] =
    def parseDefDefs: ParseResult[List[DefDef]] =
      if peekType == Def() then
        parseDefDef flatMap { ddef =>
          parseDefDefs map { ddefs => ddef :: ddefs }
        }
      else Right(Nil)
    matchAhead(LeftBrace()) flatMap { _ =>
      parseDefDefs flatMap { ddefs =>
        parseExpr flatMap { expr =>
          matchAhead(RightBrace()) map { _ => Block(ddefs, expr) }
        }
      }
    }

  def parseDefDef: ParseResult[DefDef] =
    matchAhead(Def()) flatMap { _ =>
      parseIdentifier flatMap { case Token(_, defname) =>
        step()
        parseFormalListWithImplicitsOptional flatMap { (iformals, formals) =>
          matchAhead(Colon()) flatMap { _ =>
            parseExpr flatMap { resTyp =>
              val sig = makePiType(iformals, makePiType(formals, resTyp), isImp = true)
              if peekType == Equal() then
                matchAhead(Equal()) flatMap { _ =>
                  parseExpr map { body =>
                    val args = iformals.map(_._1) ++ formals.map(_._1)
                    val term = makePiIntro(args, body)
                    DefDef(defname, sig, Some(term))
                  }
                }
              else Right(DefDef(defname, sig, None))
            }
          }
        }
      }
    }

  def parsePrintln: ParseResult[cmd.Normalise] =
    matchAhead(Println()) flatMap { _ =>
      matchAhead(LeftParen()) flatMap { _ =>
        parseExpr flatMap { body =>
          matchAhead(RightParen()).map(_ => cmd.Normalise(body))
        }
      }
    }

  def parseDef: ParseResult[Definition] =
    peekType match
      case Println() => parsePrintln
      case Def() => parseDefDef
      case Enum() => parseDataDef
      case _ => Left(s"expecting start of definition, but found $peekType")

  def parseDefs: ParseResult[List[Definition]] =
    @annotation.tailrec def recur(acc: List[Definition]): ParseResult[List[Definition]] =
      peekType match
        case EOF() => Right(acc.reverse)
        case _ => parseDef match
          case Left(err) => Left(err)
          case Right(x) => recur(x :: acc)
    recur(Nil)

object Parser:
  type ParseResult[+X] = Either[String, X]

  def parseExpr(source: String): ParseResult[Expr] =
    val parser = new Parser(source)
    parser.parseExpr

  def parseDataDef(source: String): ParseResult[DataDef] =
    val parser = new Parser(source)
    parser.parseDataDef

  def parseDefDef(source: String): ParseResult[DefDef] =
    val parser = new Parser(source)
    parser.parseDefDef

  def parseProgram(source: String): ParseResult[List[Definition]] =
    val parser = new Parser(source)
    parser.parseDefs
