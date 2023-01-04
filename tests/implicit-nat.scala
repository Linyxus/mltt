enum Eq(A: Type, a: A, b: A) extends Type:
  case Refl(A: Type, a: A) extends Eq(A, a, a)
enum Nat extends Type:
  case Zero() extends Nat()
  case Succ(n: Nat()) extends Nat()

def Nat: Type = Nat()
def Zero: Nat = Zero()

def Eqq(using A: Type)(a: A, b: A): Type = Eq(A, a, b)
def refll(using A: Type, a: A): Eqq(a, a) = Refl(A, a)

def test1: Eqq(Zero, Zero) = refll

def add(a: Nat, b: Nat): Nat = a match
  case Zero() => b
  case Succ(a0) => Succ(add(a0, b))

def symm(using A: Type, a: A, b: A)(eq: Eqq(a, b)): Eqq(b, a) = eq match
  case Refl(A, c) => refll

def trans(using A: Type, a: A, b: A, c: A)(eq1: Eqq(a, b), eq2: Eqq(b, c)): Eqq(a, c) = eq1 match
  case Refl(A, c1) => eq2 match
    case Refl(A, c2) => refll

def cong(using A: Type, B: Type, a: A, b: A)(eq: Eqq(a, b), f: (x: A) -> B): Eqq(f(a), f(b)) = eq match
  case Refl(A, c) => refll

def nAddOne(n: Nat, m: Nat): Eqq(add(n, Succ(m)), Succ(add(n, m))) = n match
  case Zero() => refll
  case Succ(n0) =>
    cong(nAddOne(n0, m), x => Succ(x))

def nAddZero(n: Nat): Eqq(add(n, Zero), n) = n match
  case Zero() => refll
  case Succ(n0) => cong(nAddZero(n0), x => Succ(x))

def addComm(a: Nat, b: Nat): Eqq(add(a, b), add(b, a)) = a match
  case Zero() => symm(nAddZero(b))
  case Succ(a0) => {
    def IH: Eqq(add(a0, b), add(b, a0)) = addComm(a0, b)
    def H1: Eqq(add(b, Succ(a0)), Succ(add(b, a0))) = nAddOne(b, a0)
    trans(cong(IH, x => Succ(x)), symm(H1))
  }
