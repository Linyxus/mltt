enum Eq(A: Type, a: A, b: A) extends Type:
  case Refl(A: Type, a: A) extends Eq(A, a, a)

def cong(
  A: Type, B: Type,
  a: A, b: A, f: (x: A) -> B,
  eq: Eq(A, a, b)
): Eq(B, f(a), f(b)) =
  eq match
    case Refl(A, c) => Refl(B, f(c))

def symm(A: Type, a: A, b: A, eq: Eq(A, a, b)): Eq(A, b, a) =
  eq match
    case Refl(A, c) => eq

def trans(
  A: Type,
  a: A,
  b: A,
  c: A,
  eq1: Eq(A, a, b),
  eq2: Eq(A, b, c)
): Eq(A, a, c) =
  eq1 match
    case Refl(A, d) =>
      eq2 match
        case Refl(A, e) => Refl(A, e)

enum Nat extends Type:
  case Zero() extends Nat()
  case Succ(n: Nat()) extends Nat()
def Nat: Type = Nat()

def add(a: Nat, b: Nat): Nat = a match
  case Zero() => b
  case Succ(a1) => Succ(add(a1, b))

def nAddZero(n: Nat): Eq(Nat, add(n, Zero()), n) = n match
  case Zero() => Refl(Nat, Zero())
  case Succ(n0) => {
    def IH: Eq(Nat, add(n0, Zero()), n0) = nAddZero(n0)
    cong(Nat, Nat, add(n0, Zero()), n0, x => Succ(x), IH)
  }

def addSucc(a: Nat, b: Nat): Eq(Nat, add(a, Succ(b)), Succ(add(a, b))) =
  a match
    case Zero() => Refl(Nat, Succ(b))
    case Succ(a0) => {
      def IH: Eq(Nat, add(a0, Succ(b)), Succ(add(a0, b))) = addSucc(a0, b)
      cong(Nat, Nat, add(a0, Succ(b)), Succ(add(a0, b)), x => Succ(x), IH)
    }

def addComm(n: Nat, m: Nat): Eq(Nat, add(n, m), add(m, n)) = n match
  case Zero() => symm(Nat, add(m, Zero()), m, nAddZero(m))
  case Succ(n0) => {
    def IH: Eq(Nat, add(n0, m), add(m, n0)) = addComm(n0, m)
    def H1: Eq(Nat, Succ(add(n0, m)), Succ(add(m, n0))) =
      cong(Nat, Nat, add(n0, m), add(m, n0), x => Succ(x), IH)
    def H2: Eq(Nat, add(m, Succ(n0)), Succ(add(m, n0))) =
      addSucc(m, n0)
    def H3: Eq(Nat, Succ(add(m, n0)), add(m, Succ(n0))) =
      symm(Nat, add(m, Succ(n0)), Succ(add(m, n0)), H2)
    trans(Nat, Succ(add(n0, m)), Succ(add(m, n0)), add(m, Succ(n0)), H1, H3)
  }

def addAssoc(a: Nat, b: Nat, c: Nat): Eq(Nat, add(a, add(b, c)), add(add(a, b), c)) =
  a match
    case Zero() => Refl(Nat, add(b, c))
    case Succ(a0) =>
      cong(Nat, Nat, add(a0, add(b, c)), add(add(a0, b), c), x => Succ(x), addAssoc(a0, b, c))
