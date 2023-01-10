enum Nat extends Type:
  case zero extends Nat
  case suc(n: Nat) extends Nat

enum Void extends Type:

def absurd(using A: Type)(void: Void): A = void match

enum Eq(using A: Type)(a: A, b: A) extends Type:
  case refl(using A: Type, a: A) extends Eq(a, a)

def Not(A: Type): Type = (x: A) -> Void

def Neq(using A: Type)(a: A, b: A): Type = Not(Eq(a, b))

def symm(using A: Type, a: A, b: A)(eq: Eq(a, b)): Eq(b, a) = eq match
  case refl => refl

def neqSymm(using A: Type, a: A, b: A)(neq: Neq(a, b)): Neq(b, a) = {
  def helper(eq: Eq(b, a)): Void = neq(symm(eq))
  helper
}

enum Typ extends Type:
  case lam(arg: Typ, res: Typ) extends Typ

enum Ctx extends Type:
  case emptyCtx extends Ctx
  case consCtx(ctx0: Ctx, typ: Typ) extends Ctx

def length(ctx: Ctx): Nat = ctx match
  case emptyCtx => zero
  case consCtx(ctx0, typ) => suc(length(ctx0))

enum Bind(ctx: Ctx, i: Nat, typ: Typ) extends Type:
  case here(using ctx: Ctx, typ: Typ) extends Bind(consCtx(ctx, typ), zero, typ)
  case there(using ctx: Ctx, i: Nat, A: Typ, B: Typ)(h0: Bind(ctx, i, A)) extends Bind(consCtx(ctx, B), suc(i), A)

enum Trm extends Type:
  case var(i: Nat) extends Trm
  case fun(body: Trm) extends Trm
  case app(func: Trm, arg: Trm) extends Trm

enum Typing(ctx: Ctx, t: Trm, typ: Typ) extends Type:
  case typedVar(using ctx: Ctx, i: Nat, A: Typ)(bind: Bind(ctx, i, A)) extends Typing(ctx, var(i), A)
  case typedFun(using ctx: Ctx, T: Typ, body: Trm, U: Typ)
               (typedBody: Typing(consCtx(ctx, T), body, U)) extends Typing(ctx, fun(body), lam(T, U))
  case typedApp(using ctx: Ctx, T: Typ, U: Typ, func: Trm, arg: Trm)
               (typedFunc: Typing(ctx, func, lam(T, U)), typedArg: Typing(ctx, arg, T))
               extends Typing(ctx, app(func, arg), U)


enum Dec(A: Type) extends Type:
  case yes(using A: Type)(a: A) extends Dec(A)
  case no(using A: Type)(na: Not(A)) extends Dec(A)

def zeroNeSuc(n: Nat): (x: Eq(zero, suc(n))) -> Void = {
  def helper(eq: Eq(zero, suc(n))): Void = eq match
    case refl => ()
  helper
}

def decEqSuc(using a: Nat, b: Nat)(dec: Dec(Eq(a, b))): Dec(Eq(suc(a), suc(b))) = dec match
  case yes(eq) => {
    eq match
      case refl => yes(refl)
  }
  case no(neq) => {
    def helper(eq: Eq(suc(a), suc(b))): Void = eq match
      case refl => neq(refl)
    no(helper)
  }

def isEqNat(a: Nat, b: Nat): Dec(Eq(a, b)) = a match
  case zero => {
    b match
      case zero => yes(refl)
      case suc(b0) => no(zeroNeSuc(b0))
  }
  case suc(a0) => {
    b match
      case zero => no(neqSymm(zeroNeSuc(a0)))
      case suc(b0) => decEqSuc(isEqNat(a0, b0))
  }

def open(trm: Trm, to: Trm, i: Nat): Trm = trm match
  case var(j) => {
    isEqNat(i, j) match
      case yes(eq) => to
      case no(neq) => var(j)
  }
  case fun(body) => fun(open(body, to, suc(i)))
  case app(f, a) => app(open(f, to, i), open(a, to, i))

enum IsValue(trm: Trm) extends Type:
  case funIsValue(body: Trm) extends IsValue(fun(body))

enum Reduce(trm1: Trm, trm2: Trm) extends Type:
  case reduceFun(using fun1: Trm, fun2: Trm, arg: Trm)
                (red: Reduce(fun1, fun2)) extends Reduce(app(fun1, arg), app(fun2, arg))
  case reduceArg(using fun: Trm, arg1: Trm, arg2: Trm)
                (Hv: IsValue(fun), red: Reduce(arg1, arg2)) extends Reduce(app(fun, arg1), app(fun, arg2))
  case reduceApp(using body: Trm, arg: Trm)(Hv: IsValue(arg)) extends Reduce(app(fun(body), arg), open(body, arg, zero))

def valueNotReduce(using t: Trm, u: Trm)(hv: IsValue(t)): Not(Reduce(t, u)) = {
  def helper(red: Reduce(t, u)): Void = hv match
    case funIsValue(body) => red match
      case reduceFun(red0) => ()
      case reduceArg(Hv0, red0) => ()
      case reduceApp(Hv0) => ()
  helper
}

enum Progress(t: Trm) extends Type:
  case step(using t: Trm, u: Trm)(red: Reduce(t, u)) extends Progress(t)
  case done(using t: Trm)(hv: IsValue(t)) extends Progress(t)

def emptyNotBind(using i: Nat, typ: Typ)(hb: Bind(emptyCtx, i, typ)): Void =
  hb match
    case here => ()
    case there(hb0) => ()

def progress(using t: Trm, typ: Typ)
            (typed: Typing(emptyCtx, t, typ)): Progress(t) = typed match
  case typedVar(hb) => absurd(emptyNotBind(hb))
  case typedFun(using ctx0, T, body, U)(hbody) => done(funIsValue(body))
  case typedApp(using ctx, T, U, func, arg)(hfunc, harg) => {
    def IHfunc = progress(hfunc)
    IHfunc match
      case step(red0) => step(reduceFun(red0))
      case done(hv) => {
        def IHarg = progress(harg)
        IHarg match
          case step(red0) => step(reduceArg(hv, red0))
          case done(hv1) => hv match
            case funIsValue(body) => step(reduceApp(hv1))
      }
  }

def ext(using ctx1: Ctx, ctx2: Ctx)
       (H: (i: Nat) ?-> (typ: Typ) ?-> (hb: Bind(ctx1, i, typ)) -> Bind(ctx2, i, typ)):
       (i: Nat) ?-> (A: Typ) ?-> (B: Typ) ?-> (hb: Bind(consCtx(ctx1, B), i, A)) -> Bind(consCtx(ctx2, B), i, A) = {
  def res(using i: Nat, A: Typ, B: Typ)(hb: Bind(consCtx(ctx1, B), i, A)): Bind(consCtx(ctx2, B), i, A) = hb match
    case here => here
    case there(hb0) => there(H(hb0))
  res
}

def rename(using ctx1: Ctx, ctx2: Ctx)
          (H: (x: Nat) ?-> (A: Typ) ?-> (hb: Bind(ctx1, x, A)) -> Bind(ctx2, x, A)):
          (t: Trm) ?-> (A: Typ) ?-> (Ht: Typing(ctx1, t, A)) -> Typing(ctx2, t, A) = {
  def res(using t: Trm, A: Typ)(ht: Typing(ctx1, t, A)): Typing(ctx2, t, A) = ht match
    case typedVar(hb) => typedVar(H(hb))
    case typedFun(using ctx, T, body, U)(hbody) => {
      def H1 = ext(H)
      def H2(using x: Nat, A: Typ)(hb: Bind(consCtx(ctx1, T), x, A)): Bind(consCtx(ctx2, T), x, A) = H1(hb)
      def IH = rename(H2)
      typedFun(IH(hbody))
    }
    case typedApp(hfunc, harg) => typedApp(rename(H, hfunc), rename(H, harg))
  res
}

def weaken(using ctx: Ctx, t: Trm, A: Typ)
          (ht: Typing(emptyCtx, t, A)):
          Typing(ctx, t, A) = {
  def H(using x: Nat, A: Typ)(hb: Bind(emptyCtx, x, A)): Bind(ctx, x, A) = absurd(emptyNotBind(hb))
  rename(H, ht)
}
