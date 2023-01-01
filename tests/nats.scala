enum Nat extends Type:
  case Zero() extends Nat()
  case Succ(n: Nat()) extends Nat()
def Nat: Type = Nat()

def add(a: Nat, b: Nat): Nat = a match
  case Zero() => b
  case Succ(a) => Succ(add(a, b))

def zero: Nat = Zero()
def one: Nat = Succ(zero)
def two: Nat = add(one, one)
def three: Nat = add(two, one)
def four: Nat = add(two, two)

def mult(a: Nat, b: Nat): Nat = a match
  case Zero() => Zero()
  case Succ(a) => add(b, mult(a, b))
def double(n: Nat): Nat = mult(two, n)

def exp(a: Nat, e: Nat): Nat = e match
  case Zero() => one
  case Succ(e) => mult(a, exp(a, e))

def ten: Nat = add(two, mult(two, four))
