package parser

sealed trait TokenType

case class Ident(name: String) extends TokenType

// braces
case class LeftParen() extends TokenType
case class RightParen() extends TokenType
case class LeftBrace() extends TokenType
case class RightBrace() extends TokenType

// arrows
case class Arrow() extends TokenType
case class QuestionArrow() extends TokenType
case class DoubleArrow() extends TokenType

// equals
case class Equal() extends TokenType

// colon, comma
case class Colon() extends TokenType
case class Comma() extends TokenType

// keywords
case class Enum() extends TokenType
case class Extends() extends TokenType
case class Case() extends TokenType
case class Def() extends TokenType
case class Match() extends TokenType
case class Println() extends TokenType
case class ThreeQuestionMarks() extends TokenType
case class Using() extends TokenType

// literals
case class NatNum(i: Int) extends TokenType

// newlines, indents
case class NewLine() extends TokenType
case class Indent() extends TokenType
case class Outdent() extends TokenType

// special
case class EOF() extends TokenType
case class ErrorToken(msg: String) extends TokenType

case class Token(tp: TokenType, content: String) {
  override def toString(): String = tp match
    case EOF() => "<eof>"
    case ErrorToken(msg) => s"<error: $msg>"
    case NewLine() => "<newline>"
    case Indent() => "<indent>"
    case Outdent() => "<outdent>"
    case _ => content
}

