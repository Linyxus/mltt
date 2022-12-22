package parser

import ast._

class Parser(source: String):
  import Parser._

  private var tokens: LazyList[Token] = Tokenizer.getTokensLazy(source)
  private def current = tokens.head
  private var indentLevel: Int = 0

  def peekType: TokenType = current.tp
  def step(): Unit =
    if peekType == Indent() then
      indentLevel += 1
    else if peekType == Outdent() then
      indentLevel -= 1
    tokens = tokens.tail
  def eof: Boolean = peekType == EOF()

  def expect(tpe: TokenType): ParseResult[Token] =
    if peekType == tpe then Right(current) else Left(s"expecting $tpe, but found $peekType")

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
      parseParamList map { args => ApplyDataCon(con.content, args) }
    }

  def parseCaseDef: ParseResult[CaseDef] =
    matchAhead(Case()) flatMap { _ =>
      parsePattern flatMap { pat =>
        matchAhead(DoubleArrow()) flatMap { _ =>
          parseExpr.map(CaseDef(pat, _))
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
                  parseExpr map { resTyp => Pi(content, argTyp, resTyp) }
                }
              }
            }
          }
      }
    }

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
        parseParamList match
          case err @ Left(_) => err.asInstanceOf
          case Right(ps) => recur(Apply(acc, ps))
      else if peekType == parser.Match() then
        step()
        Right(Match(acc, parseCaseDefs))
      else Right(acc)
    recur(e)
  }

  def parseType: ParseResult[Expr] =
    step()
    Right(Type(Level.LZero))

  def parseExprAtom: ParseResult[Expr] = peekType match
    case Ident(name) if name == "Type" => parseType
    case Ident(name) => varOrPiIntro
    case LeftParen() => parsePi
    case ErrorToken(msg) => Left(s"tokeniaztion error: $msg")
    case _ => Left(s"unexpected token type $peekType")

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

  def makePiType(args: List[(String, Expr)], resTyp: Expr): Expr =
    @annotation.tailrec def recur(xs: List[(String, Expr)], acc: Expr): Expr =
      xs match
        case Nil => acc
        case (argName, argTyp) :: xs => recur(xs, Pi(argName, argTyp, acc))
    recur(args.reverse, resTyp)

  def parseDataCon: ParseResult[ConsDef] =
    matchAhead(Case()) flatMap { _ =>
      parseIdentifier flatMap { case Token(_, name) =>
        step()
        parseFormalList flatMap { formals =>
          matchAhead(Extends()) flatMap { _ =>
            parseExpr map { resTyp =>
              ConsDef(name, makePiType(formals, resTyp))
            }
          }
        }
      }
    }

  def parseFormalListOptional: ParseResult[List[(String, Expr)]] =
    if peekType == LeftParen() then
      parseFormalList
    else Right(Nil)

  def parseDataDef: ParseResult[DataDef] =
    matchAhead(Enum()) flatMap { _ =>
      parseIdentifier flatMap { case Token(_, name) =>
        step()
        parseFormalListOptional flatMap { formals =>
          matchAhead(Extends()) flatMap { _ =>
            parseExpr flatMap { resTyp =>
              val sig = makePiType(formals, resTyp)
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

object Parser:
  type ParseResult[+X] = Either[String, X]

  def parseExpr(source: String): ParseResult[Expr] =
    val parser = new Parser(source)
    parser.parseExpr

  def parseDataDef(source: String): ParseResult[DataDef] =
    val parser = new Parser(source)
    parser.parseDataDef
