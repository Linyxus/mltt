enum Nat extends Type:
  case zero extends Nat
  case suc(n: Nat) extends Nat

enum Eq(using A: Type)(a: A, b: A) extends Type:
  case refl(using A: Type, a: A) extends Eq(a, a)

enum IsOk extends Type:
  case yes extends IsOk
  case no extends IsOk

enum Bool extends Type:
  case true extends Bool
  case false extends Bool

def isOk(i: Nat): IsOk

def check(i: Nat): Bool = isOk(i) match
  case yes => true
  case no => false

def isOkToBool(x: IsOk): Bool = x match
  case yes => true
  case no => false

def lemma(i: Nat): Eq(isOkToBool(isOk(i)), check(i)) = isOk(i) match
  case yes => refl
  case no => refl
