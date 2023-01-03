package parser

import collection.mutable.Queue

class Tokenizer(source: String):
  private var start: Int = 0
  private var current: Int = 0
  private var lineno: Int = 0
  private var col: Int = 0
  private var nextTokens: Queue[Token] = Queue.empty
  private var indentLevels: List[Int] = 0 :: Nil

  def makeToken(tp: TokenType): Token = Token(tp, source.substring(start, current))

  def emitToken(tp: TokenType): Unit = nextTokens.enqueue(makeToken(tp))

  def currentIndent: Int = indentLevels.head
  def indent(level: Int): Unit = indentLevels = level :: indentLevels
  def outdent(level: Int): Boolean =
    indentLevels = indentLevels.tail
    level == currentIndent

  def peek: Char = source(current)
  def isEof: Boolean = current >= source.length
  def forward: Char =
    val res = peek
    step()
    res
  def step(): Unit =
    if peek == '\n' then
      lineno += 1
      col = 0
    else
      col += 1
    current += 1

  def scanWhitespaces: Unit =
    var skipped = false
    var newline = false
    while !isEof && peek.isWhitespace do
      if peek == '\n' then newline = true
      skipped = true
      step()
    if newline then
      if col == currentIndent then
        // emitToken(NewLine())
        ()
      else if col > currentIndent then
        indent(col)
        // emitToken(Indent())
      else
        if outdent(col) then
          // emitToken(Outdent())
          ()
        else
          // emitToken(ErrorToken(s"Invalid indent: $col"))
          ()

  def scanIdentifier(): Unit =
    val stop_chars = ":(){},".toSet
    while !isEof && !peek.isWhitespace && !stop_chars.contains(peek) do
      step()
    val content = source.substring(start, current)
    emitToken(keywords.get(content).getOrElse(Ident(content)))

  val keywords: Map[String, TokenType] = Map(
    "enum" -> Enum(),
    "extends" -> Extends(),
    "case" -> Case(),
    "def" -> Def(),
    "match" -> Match(),
    "println" -> Println(),
    "???" -> ThreeQuestionMarks(),
    "?->" -> QuestionArrow(),
    "using" -> Using(),
  )

  def expect(ch: Char): Boolean =
    if peek == ch then
      step()
      true
    else false

  def scanNumber(): Unit =
    while !isEof && peek.isDigit do step()
    val num = source.substring(start, current).toInt
    emitToken(NatNum(num))

  def scanNext(): Unit =
    if isEof then emitToken(EOF())
    else
      start = current
      scanWhitespaces

      if !isEof then
        start = current

        forward match
          case '(' => emitToken(LeftParen())
          case ')' => emitToken(RightParen())
          case '{' => emitToken(LeftBrace())
          case '}' => emitToken(RightBrace())
          case '-' =>
            if expect('>') then
              emitToken(Arrow())
            else
              emitToken(ErrorToken("Expecting `>` after `-`"))
          case '=' =>
            if expect('>') then
              emitToken(DoubleArrow())
            else
              emitToken(Equal())
          case ':' => emitToken(Colon())
          case ',' => emitToken(Comma())
          case ch if ch.isDigit => scanNumber()
          case _ => scanIdentifier()
        else emitToken(EOF())

  def nextToken: Token =
    if nextTokens.isEmpty then scanNext()
    nextTokens.dequeue()

object Tokenizer:
  def getTokens(source: String): List[Token] =
    val tokenizer = new Tokenizer(source)
    def recur(cb: List[Token] => List[Token]): List[Token] =
      tokenizer.nextToken match
        case Token(EOF(), _) => cb(Nil)
        case tk => recur(xs => cb(tk :: xs))
    recur(xs => xs)

  def getTokensLazy(source: String): LazyList[Token] =
    val tokenizer = new Tokenizer(source)
    def recur: LazyList[Token] =
      tokenizer.nextToken match
        case tk @ Token(EOF(), _) => tk #:: LazyList.empty
        case tk => tk #:: recur
    recur

