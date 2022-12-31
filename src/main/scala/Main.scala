import driver.Driver._

@main def run(): Unit = {
  val source = """
enum Eq(A: Type, a: A, b: A) extends Type:
  case Refl(A: Type, a: A) extends Eq(A, a, a)

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
    case Zero() => ???
    case Succ(n0) => ???
"""
  println(check(source))
}
