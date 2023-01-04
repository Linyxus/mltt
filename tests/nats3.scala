enum Nat extends Type:
  case Zero extends Nat
  case Succ(n: Nat) extends Nat

enum Eq(using A: Type)(a: A, b: A) extends Type:
  case refl(using A: Type, a: A) extends Eq(a, a)

def symm(using A: Type, a: A, b: A)(eq: Eq(a, b)): Eq(b, a) = eq match
  case refl => refl

def trans(using A: Type, a: A, b: A, c: A)(eq1: Eq(a, b), eq2: Eq(b, c)): Eq(a, c) = eq1 match
  case refl => eq2 match
    case refl => refl

def cong(using A: Type, B: Type, a: A, b: A)(eq: Eq(a, b), f: (x: A) -> B): Eq(f(a), f(b)) = eq match
  case refl => refl

def add(a: Nat, b: Nat) = a match
  case Zero => b
  case Succ(a0) => Succ(add(a0, b))

def nAddZero(n: Nat): Eq(add(n, Zero), n) = n match
  case Zero => refl
  case Succ(n0) => {
    def IH = nAddZero(n0)
    cong(IH, x => Succ(x))
  }

def nAddSucc(n: Nat, m: Nat): Eq(add(n, Succ(m)), Succ(add(n, m))) = n match
  case Zero => refl
  case Succ(n0) => {
    def IH = nAddSucc(n0, m)
    cong(IH, x => Succ(x))
  }

def addComm(a: Nat, b: Nat): Eq(add(a, b), add(b, a)) = a match
  case Zero => symm(nAddZero(b))
  case Succ(a0) => {
    def IH = addComm(a0, b)
    def H0 = nAddSucc(b, a0)
    def H1 = cong(IH, x => Succ(x))
    def H2 = symm(H0)
    trans(H1, H2)
  }

def addAssoc(a: Nat, b: Nat, c: Nat): Eq(add(a, add(b, c)), add(add(a, b), c)) = a match
  case Zero => refl
  case Succ(a0) => cong(addAssoc(a0, b, c), x => Succ(x))

def double(n: Nat): Nat = n match
  case Zero => Zero
  case Succ(n0) => Succ(Succ(double(n0)))

def addDoubleEquiv(n: Nat): Eq(add(n, n), double(n)) = n match
  case Zero => refl
  case Succ(n0) => {
    def IH = addDoubleEquiv(n0)
    def H1 = cong(nAddSucc(n0, n0), x => Succ(x))
    def H2 = cong(IH, x => Succ(Succ(x)))
    trans(H1, H2)
  }

enum IsEven(n: Nat) extends Type:
  case zero extends IsEven(Zero)
  case suc(using m: Nat)(isEven: IsEven(m)) extends IsEven(Succ(Succ(m)))

enum IsOdd(n: Nat) extends Type:
  case one extends IsOdd(Succ(Zero))
  case suc(using m: Nat)(isOdd: IsOdd(m)) extends IsOdd(Succ(Succ(m)))

def addEvenEven(using a: Nat, b: Nat)(
  aIsEven: IsEven(a), bIsEven: IsEven(b)): IsEven(add(a, b)) = aIsEven match
  case zero => bIsEven
  case suc(a0IsEven) => {
    def IH = addEvenEven(a0IsEven, bIsEven)
    suc(IH)
  }

def addEvenOdd
  (using a: Nat, b: Nat)
  (aIsEven: IsEven(a), bIsOdd: IsOdd(b)):
  IsOdd(add(a, b)) = aIsEven match
  case zero => bIsOdd
  case suc(using a0)(a0IsEven) => suc(addEvenOdd(a0IsEven, bIsOdd))

def succOddIsEven(using n: Nat)
  (nIsOdd: IsOdd(n)):
  IsEven(Succ(n)) = n match
  case Zero => {
    nIsOdd match
      case one => ()
      case suc(n0IsOdd) => ()
  }
  case Succ(n0) => nIsOdd match
    case one => suc(zero)
    case suc(nIsOdd1) => {
      def IH = succOddIsEven(nIsOdd1)
      suc(IH)
    }

def addOddOdd
  (using a: Nat, b: Nat)
  (aIsOdd: IsOdd(a), bIsOdd: IsOdd(b)):
  IsEven(add(a, b)) = aIsOdd match
  case one => succOddIsEven(bIsOdd)
  case suc(using a0)(a0IsOdd) => suc(addOddOdd(a0IsOdd, bIsOdd))
