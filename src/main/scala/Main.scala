import driver.Driver._

@main def run(): Unit = {
  val source = """
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

  val source1 = """
enum Nat extends Type:
  case zero extends Nat
  case suc(n: Nat) extends Nat

enum Void extends Type:

enum Typ extends Type:
  case lam(arg: Typ, res: Typ) extends Typ
  case nat extends Typ

enum Ctx extends Type:
  case emptyCtx extends Ctx
  case consCtx(ctx0: Ctx, typ: Typ) extends Ctx

enum InEnv(ctx: Ctx, typ: Typ) extends Type:
  case here(using ctx: Ctx, typ: Typ) extends InEnv(consCtx(ctx, typ), typ)
  case there(using ctx: Ctx, A: Typ, B: Typ)(h0: InEnv(ctx, A)) extends InEnv(consCtx(ctx, B), A)

enum Trm(ctx: Ctx, typ: Typ) extends Type:
  case var(using ctx: Ctx, A: Typ)(inenv: InEnv(ctx, A)) extends Trm(ctx, A)
  case fun(using ctx: Ctx, A: Typ, B: Typ)
          (typBody: Trm(consCtx(ctx, A), B))
          extends Trm(ctx, lam(A, B))
  case app(using ctx: Ctx, A: Typ, B: Typ)
          (func: Trm(ctx, lam(A, B)), arg: Trm(ctx, A))
          extends Trm(ctx, B)
  case zero(using ctx: Ctx) extends Trm(ctx, nat)
  case suc(using ctx: Ctx)(pred: Trm(ctx, nat)) extends Trm(ctx, nat)
  case cs(using ctx: Ctx, A: Typ)
         (n: Trm(ctx, nat), init: Trm(ctx, A), update: Trm(consCtx(ctx, nat), A))
         extends Trm(ctx, A)
  case rec(using ctx: Ctx, A: Typ)
          (h0: Trm(consCtx(ctx, A), A))
          extends Trm(ctx, A)

def length(ctx: Ctx): Nat = ctx match
  case emptyCtx => zero
  case consCtx(ctx0, A) => suc(length(ctx0))

def ext(using ctx1: Ctx, ctx2: Ctx)
       (H: (A: Typ) ?-> (inenv: InEnv(ctx1, A)) -> InEnv(ctx2, A)):
       (A: Typ) ?-> (B: Typ) ?-> (inenv: InEnv(consCtx(ctx1, B), A)) -> InEnv(consCtx(ctx2, B), A) =
  A => B => inenv => {
    inenv match
      case here => here
      case there(inenv0) => {
        def inenv1 = H(inenv0)
        there(inenv1)
      }
  }

def subst(using ctx1: Ctx, ctx2: Ctx)
         (H: (A: Typ) ?-> (inenv: InEnv(ctx1, A)) -> Trm(ctx2, A)):
         (A: Typ) ?-> (trm: Trm(ctx1, A)) -> Trm(ctx2, A) = A => t => t match
  case var(inenv) => H(inenv)
  case fun(body) => fun(???)
"""

  // case app(func, arg) => ???
  // case zero => ???
  // case suc(pred) => ???
  // case cs(n, init, update) => ???
  // case rec(t0) => ???

  runTypecheck(source1)
}
