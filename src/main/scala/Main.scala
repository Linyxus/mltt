import driver.Driver._

@main def run(): Unit = {
  val source = """
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
"""
  val source1 = """
enum Nat extends Type:
  case Zero() extends Nat()
  case Succ(n: Nat()) extends Nat()
def Nat: Type = Nat()
def Zero: Nat = Zero()

enum Typ extends Type:
  case lam(arg: Typ(), res: Typ()) extends Typ()
def Typ: Type = Typ()

enum Trm extends Type:
  case var(i: Nat) extends Trm()
  case fun(argTyp: Typ, body: Trm()) extends Trm()
  case app(fun: Trm(), arg: Trm()) extends Trm()
def Trm: Type = Trm()

enum Ctx extends Type:
  case emptyCtx() extends Ctx()
  case consCtx(t: Typ, ctx0: Ctx()) extends Ctx()
def Ctx: Type = Ctx()
def emptyCtx: Ctx = emptyCtx()

enum Bind(i: Nat, typ: Typ, ctx: Ctx) extends Type:
  case bindHere(typ: Typ, ctx0: Ctx) extends Bind(Zero, typ, consCtx(typ, ctx0))
  case bindThere(i: Nat, typ0: Typ, typ: Ctx, ctx0: Ctx, bind: Bind(i, typ, ctx0)) extends Bind(Succ(i), typ, consCtx(typ0, ctx0))

enum Typed(ctx: Ctx, t: Trm, typ: Typ) extends Type:
  case typedVar(ctx: Ctx, i: Nat, typ: Typ, bind: Bind(i, typ, ctx)) extends Typed(ctx, var(i), typ)
  case typedFun(
    ctx: Ctx, T: Typ, t: Trm, U: Typ,
    typedBody: Typed(consCtx(T, ctx), t, U)) extends Typed(ctx, fun(T, t), lam(T, U))
  case typedApp(
    ctx: Ctx, fun: Trm, T: Typ, U: Typ, arg: Trm,
    typedFun: Typed(ctx, fun, lam(T, U)),
    typedArg: Typed(ctx, arg, T)) extends Typed(ctx, app(fun, arg), U)

enum Reduce(t: Trm, t1: Trm) extends Type:
  case reduceApp(T: Typ, t: Trm, u: Trm) extends Reduce(app(fun(T, t), u), ???)
"""

  println(check(source))
}
