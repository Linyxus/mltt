enum Void extends Type:
def Void: Type = Void()
def not(A: Type): Type = (x: A) -> Void
def contradict(A: Type, a: A, na: not(A)): Void = na(a)
def absurd(A: Type, bad: Void): A = bad match

enum Exists(A: Type, B: (x: A) -> Type) extends Type:
  case exists(A: Type, B: (x: A) -> Type, x: A, y: B(x)) extends Exists(A, B)

enum Or(A: Type, B: Type) extends Type:
  case Left(A: Type, B: Type, a: A) extends Or(A, B)
  case Right(A: Type, B: Type, b: B) extends Or(A, B)

def excludedMiddle(A: Type): Or(A, not(A))

def drinkerParadox(
  A: Type,
  isDrinking: (x: A) -> Type,
  x: A): Exists(A, x => (px: isDrinking(x)) -> (y: A) -> isDrinking(y)) = {
  def anyoneNotDrinking: Type = Exists(A, x => not(isDrinking(x)))
  excludedMiddle(anyoneNotDrinking) match
    case Left(Y, N, yes) => {
      yes match
        case exists(A0, P0, x0, x0IsNotDrinking) =>
          exists(
            A, x => (px: isDrinking(x)) -> (y: A) -> isDrinking(y),
            x0, {
              def helper(px0: isDrinking(x0), y: A): isDrinking(y) =
                absurd(isDrinking(y), contradict(isDrinking(x0), px0, x0IsNotDrinking))
              helper
            }
          )
    }
    case Right(Y, N, everyOneDrinking) => exists(
      A, x => (px: isDrinking(x)) -> (y: A) -> isDrinking(y),
      x, {
        def helper(px: isDrinking(x), y: A): isDrinking(y) =
          excludedMiddle(isDrinking(y)) match
            case Left(Y, N, yes) => yes
            case Right(Y, N, no) =>
              absurd(isDrinking(y), everyOneDrinking(exists(A, z => (px: isDrinking(z)) -> Void, y, no)))
        helper
      }
    )
}
