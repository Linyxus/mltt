import ast._
import typer._
import Level._
import core._
import Context._
import parser._
import ast.{TypedExprs => tpd}


def example(): Unit = {
  val typer = new Typer

  // val e1 = Type(LZero)
  // println(typer.typed(e1)(using Context()))

  // val e2 = PiIntro("x", Var("x"))
  // val pt2 = tpd.PiType("x", tpd.Type(LZero), tpd.Type(LZero))
  // println(typer.typed(e2, pt2)(using Context()))

  // val e3 = PiIntro("f", PiIntro("x", Apply(Var("f"), Var("x") :: Nil)))
  // val pt3 = Pi("f", Pi("z", Type(LZero), Type(LZero)), Pi("x", Type(LZero), Type(LZero)))
  // val tpt3 = typer.typed(pt3)(using Context())
  // println(tpt3)
  // println(typer.typed(e3, tpt3.getOrElse(null))(using Context()))

  // locally {
  //   val e = PiIntro("A", PiIntro("f", PiIntro("x", Apply(Var("f"), Apply(Var("f"), Var("x") :: Nil) :: Nil))))
  //   val pt = Pi("A", Type(LZero), Pi("f", Pi("x", Var("A"), Var("A")), Pi("x", Var("A"), Var("A"))))
  //   val tpt = typer.typed(pt)(using Context())
  //   println(tpt)
  //   println(typer.typed(e, tpt.getOrElse(null))(using Context()))
  // }

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
  // println(res4.map(_.constructors))

  // val def5 = DataDef(
  //   "List",
  //   Pi("A", Type(LZero), Type(LZero)),
  //   List(
  //     ConsDef("nil", Pi("A", Type(LZero), ApplyTypeCon("List", Var("A") :: Nil))),
  //     ConsDef(
  //       "cons",
  //       Pi(
  //         "A", Type(LZero),
  //         Pi(
  //           "x", Type(LZero),
  //           Pi(
  //             "xs", ApplyTypeCon("List", Var("A") :: Nil),
  //             ApplyTypeCon("List", Var("A") :: Nil)
  //           )
  //         )
  //       )
  //     )
  //   )
  // )
  // val res5 = typer.typedDataDef(def5)(using Context())
  // println(res5)
  // println(res5.map(_.constructors))
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

def defdefs = List(
  """
def add(x: Nat, y: Nat): Nat = x
""",
  """
def twice(A: Type, f: (x: A) -> A): (x: A) -> A =
  x => f(f(x))
""",
  """
def zero(A: Type, f: (x: A) -> A, x: A): A = x
""",
  """
def succ(
  n: (A: Type) -> (f: (x: A) -> A) -> (x: A) -> A,
  A: Type,
  f: (x: A) -> A,
  x: A
): A = f(n(A, f, x))
""",
)

val progs = List()

def parserExample(): Unit =
  // val tokens = Tokenizer.getTokens(prog2)
  // println(tokens)

  // val e1 = Parser.parseExpr(expr1)
  // println(e1)

  // val e2 = Parser.parseExpr(expr3)
  // println(e2)

  // for ddef <- ddefs do {
  //   println("==========")
  //   println(ddef)
  //   println("----------")
  //   val x = Parser.parseDataDef(ddef)
  //   println(x)
  // }

  // for ddef <- defdefs do {
  //   println("==========")
  //   println(ddef)
  //   println("----------")
  //   val x = Parser.parseDefDef(ddef)
  //   println(x)
  // }

  for prog <- progs do {
    println("==========")
    println(prog)
    println("----------")
    val x = Parser.parseProgram(prog)
    println(x)
  }

def typerExample(): Unit =
  val progs =
    """
enum Nat extends Type:
  case Zero() extends Nat()
  case Succ(pred: Nat()) extends Nat()

println(Nat())
println(Zero())
println(Succ(Zero()))
""" :: """
enum Nat extends Type:
  case Zero() extends Nat()
  case Succ(pred: Nat()) extends Nat()

def nat: Type = Nat()
def add2(n: Nat()): Nat() = Succ(Succ(n))
println(nat)
""" :: """
enum Nat extends Type:
  case Zero() extends Nat()
  case Succ(pred: Nat()) extends Nat()

enum List(A: Type) extends Type:
  case Nil(A: Type) extends List(A)
  case Cons(A: Type, head: A, tail: List(A)) extends List(A)

def zero: Nat() = Zero()
def one: Nat() = Succ(zero)
println(one)

def l1: List(Nat()) = Nil(Nat())
println(l1)

def l2: List(Nat()) = Cons(Nat(), zero, l1)
println(l2)
""" :: """
def zero(
  A: Type,
  f: (x: A) -> A,
  x: A
): A = x
def succ(
  n: (A: Type) -> (f: (x: A) -> A) -> (x: A) -> A,
  A: Type,
  f: (x: A) -> A,
  x: A
): A = f(n(A, f, x))

println(zero)
println(succ(zero))
println(succ(succ(zero)))
""" :: Nil
  for prog <- progs do
    println("==========")
    println(prog)
    println("----------")
    val x = Parser.parseProgram(prog)
    println(x)
    x map { defs =>
      println(s"* parsed defs: $defs")
      val typer = new Typer
      val res = typer.typedProgram(defs)(using Context())
      println(res)
    }

@main def hello: Unit = 
  // example()
  // parserExample()
  typerExample()