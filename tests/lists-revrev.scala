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
      def IH: Eq(List(A), rev(A, snoc(A, x, ys)), Cons(A, x, rev(A, ys))) = revSnoc(A, x, ys)
      def f(xs: List(A)): List(A) = snoc(A, y, xs)
      def IH1: Eq(List(A), snoc(A, y, rev(A, snoc(A, x, ys))), snoc(A, y, Cons(A, x, rev(A, ys)))) =
        cong(List(A), List(A), rev(A, snoc(A, x, ys)), Cons(A, x, rev(A, ys)), f, IH)
      IH1
    }

def revrev(A: Type, xs: List(A)): Eq(List(A), xs, rev(A, rev(A, xs))) = xs match
  case Nil(A) => Refl(List(A), Nil(A))
  case Cons(A, y, ys) => {
    def IH: Eq(List(A), ys, rev(A, rev(A, ys))) = revrev(A, ys)
    def Hsnoc: Eq(List(A), rev(A, snoc(A, y, rev(A, ys))), Cons(A, y, rev(A, rev(A, ys)))) =
      revSnoc(A, y, rev(A, ys))
    def IH1: Eq(List(A), rev(A, rev(A, ys)), ys) = symm(List(A), ys, rev(A, rev(A, ys)), IH)
    def IH2: Eq(List(A), Cons(A, y, rev(A, rev(A, ys))), Cons(A, y, ys)) =
      cong(List(A), List(A), rev(A, rev(A, ys)), ys, x => Cons(A, y, x), IH1)
    def H1: Eq(List(A), rev(A, snoc(A, y, rev(A, ys))), Cons(A, y, ys)) =
      trans(List(A), rev(A, snoc(A, y, rev(A, ys))), Cons(A, y, rev(A, rev(A, ys))), Cons(A, y, ys), Hsnoc, IH2)
    symm(List(A), rev(A, snoc(A, y, rev(A, ys))), Cons(A, y, ys), H1)
  }

