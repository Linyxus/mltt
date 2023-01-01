enum Prod(A: Type, B: (a: A) -> Type) extends Type:
  case Pair(A: Type, B: (a: A) -> Type, a: A, b: B(a)) extends Prod(A, B)

enum Nat extends Type:
  case Zero() extends Nat()
  case Succ(n: Nat()) extends Nat()
def Nat: Type = Nat()

enum Vec(A: Type, l: Nat) extends Type:
  case Nil(A: Type) extends Vec(A, Zero())
  case Cons(A: Type, l: Nat, head: A, tail: Vec(A, l)) extends Vec(A, Succ(l))

def List(A: Type): Type =
  Prod(Nat, l => Vec(A, l))

def nil(A: Type): List(A) =
  Pair(Nat, l => Vec(A, l), Zero(), Nil(A))
