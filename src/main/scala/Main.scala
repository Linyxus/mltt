import driver.Driver._

@main def run(): Unit = {
  val source = """
enum Eq(A: Type, a: A, b: A) extends Type:
  case Refl(A: Type, a: A) extends Eq(A, a, a)

def symm(A: Type, a: A, b: A, eq: Eq(A, a, b)): Eq(A, b, a) =
  eq match
    case Refl(A, c) => eq

def trans(
  A: Type, a: A, b: A, c: A,
  eq1: Eq(A, a, b),
  eq2: Eq(A, b, c)): Eq(A, a, c) =
  eq1 match
    case Refl(A, x) =>
      eq2 match
        case Refl(A, y) => Refl(A, b)

enum Nat extends Type:
  case Zero() extends Nat()
  case Succ(n: Nat()) extends Nat()
def Nat: Type = Nat()
def Zero: Nat = Zero()
def EqN(a: Nat, b: Nat): Type = Eq(Nat, a, b)
println(EqN)

def add(a: Nat, b: Nat): Nat = a match
  case Zero() => b
  case Succ(a) => Succ(add(a, b))
println(add)

def lemma1(n: Nat): EqN(n, add(n, Zero)) =
  n match
    case Zero() => Refl(Nat, Zero())
    case Succ(n0) => ???
"""
  val source1 = """
enum Eq(A: Type, a: A, b: A) extends Type:
  case Refl(A: Type, a: A) extends Eq(A, a, a)

def cong(
  A: Type, B: Type,
  a: A, b: A, f: (x: A) -> B,
  eq: Eq(A, a, b)
): Eq(B, f(a), f(b)) =
  eq match
    case Refl(A, c) => Refl(B, f(c))

def transp(
  A: Type, P: (x: A) -> Type,
  a: A, b: A,
  eq: Eq(A, a, b),
  pa: P(b)
): P(b) = eq match
  case Refl(A, c) => pa

enum List(A: Type) extends Type:
  case Nil(A: Type) extends List(A)
  case Cons(A: Type, head: A, tail: List(A)) extends List(A)

def snoc(A: Type, x: A, xs: List(A)): List(A) = xs match
  case Nil(A) => Cons(A, x, Nil(A))
  case Cons(A, y, ys) => Cons(A, y, snoc(A, x, ys))

def rev(A: Type, xs: List(A)): List(A) = xs match
  case Nil(A) => Nil(A)
  case Cons(A, y, ys) => snoc(A, y, rev(A, ys))

def revSnoc(A: Type, x: A, xs: List(A)): Eq(List(A), rev(A, snoc(A, x, xs)), Cons(A, x, rev(A, xs))) =
  xs match
    case Nil(A) => Refl(List(A), Cons(A, x, Nil(A)))
    case Cons(A, y, ys) => {
      ???
    }
"""
// def revrev(A: Type, xs: List(A)): Eq(List(A), xs, rev(A, rev(A, xs))) = xs match
//   case Nil(A) => Refl(List(A), Nil(A))
//   case Cons(A, y, ys) => ???
  println(check(source1))
}
