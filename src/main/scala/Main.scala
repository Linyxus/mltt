import ast._
import typer._
import Level._
import core._
import Context._
import parser._

def example(): Unit = {
  val typer = new Typer

  val e1 = Type(LZero)
  println(typer.typed(e1)(using Context()))

  val e2 = PiIntro("x", Var("x"))
  val pt2 = Pi("x", Type(LZero), Type(LZero))
  println(typer.typed(e2, pt2)(using Context()))

  val e3 = PiIntro("f", PiIntro("x", Apply(Var("f"), Var("x") :: Nil)))
  val pt3 = Pi("f", Pi("z", Type(LZero), Type(LZero)), Pi("x", Type(LZero), Type(LZero)))
  println(typer.typed(e3, pt3)(using Context()))

  val def4 = DataDef(
    "Nat",
    Type(LZero),
    List(
      ConsDef("zero", ApplyTypeCon("Nat", Nil)),
      ConsDef("suc", Pi("pred", ApplyTypeCon("Nat", Nil), ApplyTypeCon("Nat", Nil))),
    )
  )
  val res4 = typer.typedDataDef(def4)(using Context())
  println(res4)
  println(res4.map(_.constructors))

  val def5 = DataDef(
    "List",
    Pi("A", Type(LZero), Type(LZero)),
    List(
      ConsDef("nil", Pi("A", Type(LZero), ApplyTypeCon("List", Var("A") :: Nil))),
      ConsDef(
        "cons",
        Pi(
          "A", Type(LZero),
          Pi(
            "x", Type(LZero),
            Pi(
              "xs", ApplyTypeCon("List", Var("A") :: Nil),
              ApplyTypeCon("List", Var("A") :: Nil)
            )
          )
        )
      )
    )
  )
  val res5 = typer.typedDataDef(def5)(using Context())
  println(res5)
  println(res5.map(_.constructors))
}

val prog1 = """
enum Nat extends Type:
  case Zero() extends Nat
  case Succ(pred: Nat) extends Nat

def add(x: Nat, y: Nat) = x match
  case Zero() => y
  case Succ(x0) => Succ(add(x0, y))
"""

val prog2 = """
enum List(A: Type) extends Type:
  case Nil(A: Type) extends List(A)
  case Cons(A: Type, x: A, xs: List(A)) extends List(A)

def snoc(A: Type, x: A, xs: List(A)): List(A) = xs match
  case Nil(A) => Cons(A, x, Nil(A))
  case Cons(A, y, ys) => Cons(y, snoc(A, x, ys))
"""

val expr1 = """
(x: y) -> z
"""

val expr2 = """
x => y => z(Type(abc), b, c(d, e, f)(x => x))
"""

val expr3 = """
f(x) match
  case Zero() => x
  case Succ(x0) => y
"""

def ddefs = List(
  """
enum List(A: Type) extends Type:
  case Nil(A: Type) extends List(A)
  case Cons(A: Type, x: A, xs: List(A)) extends List(A)
""",
  """
enum Nat extends Type:
  case Zero() extends Nat
  case Succ(pred: Nat) extends Nat
""",
  """
enum Eq(A: Set, a: A, b: A) extends Type:
  case Refl(A: Set, a: A) extends Eq(A, a, a)
"""
)

def parserExample(): Unit =
  val tokens = Tokenizer.getTokens(prog2)
  println(tokens)

  val e1 = Parser.parseExpr(expr1)
  println(e1)

  val e2 = Parser.parseExpr(expr3)
  println(e2)

  for ddef <- ddefs do {
    println("==========")
    println(ddef)
    println("----------")
    val x = Parser.parseDataDef(ddef)
    println(x)
  }

@main def hello: Unit = 
  // example()
  parserExample()
