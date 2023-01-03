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

def l0: Level = lzero
def l1: Level = lsuc(lzero)
def Rel(X: Type): Type(l1) = (a: X) -> (b: X) -> Type

def isFunctional(A: Type, R: Rel(A)): Type(l0) =
  (x: A) -> (y1: A) -> (y2: A) -> (r1: R(x, y1)) -> (r2: R(x, y2)) -> Eq(A, y1, y2)

enum NextNat(a: Nat, b: Nat) extends Type:
  case nextNat(i: Nat) extends NextNat(i, Succ(i))

def nextNatIsFunctional: isFunctional(Nat, a => b => NextNat(a, b)) = {
  def evidence(x: Nat, y1: Nat, y2: Nat, p1: NextNat(x, y1), p2: NextNat(x, y2)): Eq(Nat, y1, y2) = p1 match
    case nextNat(i1) => p2 match
      case nextNat(i2) => Refl(Nat, Succ(x))
  evidence
}

enum LessThan(a: Nat, b: Nat) extends Type:
  case ltZero(i: Nat) extends LessThan(Zero(), i)
  case ltSucc(i: Nat, j: Nat, pred: LessThan(i, j)) extends LessThan(Succ(i), Succ(j))

def isReflexive(X: Type, R: Rel(X)): Type =
  (x: X) -> R(x, x)

def lessThanIsReflexive: isReflexive(Nat, a => b => LessThan(a, b)) = {
  def helper(x: Nat): LessThan(x, x) = x match
    case Zero() => ltZero(Zero())
    case Succ(x0) => ltSucc(x0, x0, helper(x0))
  helper
}

def isTransitive(X: Type, R: Rel(X)): Type =
  (x: X) -> (y: X) -> (z: X) ->
  (r1: R(x, y)) -> (r2: R(y, z)) ->
  R(x, z)

def lessThanSucc(x: Nat, y: Nat, lt: LessThan(x, y)): LessThan(x, Succ(y)) =
  lt match
    case ltZero(i) => ltZero(Succ(y))
    case ltSucc(i, j, pred) => ltSucc(i, Succ(j), lessThanSucc(i, j, pred))

def succLessThan(x: Nat, y: Nat, lt: LessThan(Succ(x), y)): LessThan(x, y) =
  lt match
    case ltZero(i) => ()
    case ltSucc(i, j, pred) => lessThanSucc(i, j, pred)

def lessThanIsTransitive: isTransitive(Nat, a => b => LessThan(a, b)) = {
  def helper(x: Nat, y: Nat, z: Nat, r1: LessThan(x, y), r2: LessThan(y, z)): LessThan(x, z) =
    r1 match
      case ltZero(y1) => ltZero(z)
      case ltSucc(x0, y0, r10) => r2 match
        case ltZero(z) => ()
        case ltSucc(y0, z0, r20) => ltSucc(x0, z0, helper(x0, y0, z0, r10, r20))
  helper
}
