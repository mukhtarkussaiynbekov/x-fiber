package cs320

import Value._

trait ExceptionHandler
case class Handler(val exp: Expr, val env: Env, val k: Cont, h: Option[Handler]) extends ExceptionHandler

object Implementation extends Template {

  def numVop(op: (BigInt, BigInt) => BigInt, excludeZero: Boolean): (Value, Value) => IntV = (_,_) match {
    case (IntV(x), IntV(y)) => if (excludeZero && y == 0) error(s"second argument is zero") else IntV(op(x,y))
    case (x, y) => error(s"not both numbers: $x, $y")
  }

  def numVCompOp(op: (BigInt, BigInt) => Boolean): (Value, Value) => BooleanV = (_,_) match {
    case (IntV(x), IntV(y)) => BooleanV(op(x,y))
    case (x, y) => error(s"not both numbers: $x, $y")
  }

  val intVAdd = numVop(_ + _, false)
  val intVMul = numVop(_ * _, false)
  val intVDiv = numVop(_ / _, true)
  val intVMod = numVop(_ % _, true)
  val intVEq = numVCompOp(_ == _)
  val intVLt = numVCompOp(_ < _)

  def interp(expr: Expr, env: Env, k: Cont, hr: Option[Handler] = None): Value = expr match {
    case Id(x) => k(env.getOrElse(x, error(s"free identifier: $x")))
    case IntE(v) => k(IntV(v))
    case BooleanE(v) => k(BooleanV(v))
    case Add(l, r) => interp(l, env, lv =>
                            interp(r, env, rv => k(intVAdd(lv, rv)), hr), hr)
    case Mul(l, r) => interp(l, env, lv =>
                            interp(r, env, rv => k(intVMul(lv, rv)), hr), hr)
    case Div(l, r) => interp(l, env, lv =>
                            interp(r, env, rv => k(intVDiv(lv, rv)), hr), hr)
    case Mod(l, r) => interp(l, env, lv =>
                            interp(r, env, rv => k(intVMod(lv, rv)), hr), hr)
    case Eq(l, r) => interp(l, env, lv =>
                            interp(r, env, rv => k(intVEq(lv, rv)), hr), hr)
    case Lt(l, r) => interp(l, env, lv =>
                            interp(r, env, rv => k(intVLt(lv, rv)), hr), hr)
    case If(c, t, f) => interp(c, env, _ match {
      case BooleanV(true) => interp(t, env, k, hr)
      case BooleanV(false) => interp(f, env, k, hr)
      case v => error(s"not a condition: $v")
    }, hr)
    case TupleE(exprs) => exprs match {
      case Nil => k(TupleV(Nil))
      case (h: Expr) :: t => interp(h, env, hv => interp(TupleE(t), env, _ match {
        case TupleV(tl) => k(TupleV(hv :: tl))
        case tv => k(tv)
      }, hr), hr)
    }
    case Proj(e, i) => interp(e, env, _ match {
      case TupleV(vs) => if (vs.length >= i) k(vs(i-1)) else error(s"index out of range: $i")
      case v => error(s"not a tuple: $v")
    }, hr)
    case NilE => k(NilV)
    case ConsE(h, t) => 
      interp(h, env, head => interp(t, env, tail =>
        tail match {
          case ConsV(_, _) | NilV => k(ConsV(head, tail))
          case v => error(s"not a list: $v")
        }, hr), hr)
    case Empty(e) => interp(e, env, _ match {
      case NilV => k(BooleanV(true))
      case ConsV(_, _) => k(BooleanV(false))
      case v => error(s"not a list: $v")
    }, hr)
    case Head(e) => interp(e, env, _ match {
      case ConsV(h, _) => k(h)
      case v => error(s"not non-empty list: $v")
    }, hr)
    case Tail(e) => interp(e, env, _ match {
      case ConsV(_, t) => k(t)
      case v => error(s"not non-empty list: $v")
    }, hr)
    case Val(x, e, b) => interp(e, env, ev => interp(b, env + (x -> ev), k, hr), hr)
    case Vcc(x, b) => interp(b, env + (x -> ContV(k)), k, hr)
    case Fun(params, body) => k(CloV(params, body, env))
    case RecFuns(funcs, body) => 
      val closures = funcs.map(f => CloV(f.parameters, f.body, env))
      val mappings = closures.zipWithIndex.map {case (clov, idx) => funcs(idx).name -> clov}
      val nenv = env ++ mappings.toMap
      closures.foreach {case clov => clov.env = nenv}
      interp(body, nenv, k, hr)
    case App(f, args) => interp(f, env, fv =>
      fv match {
        case CloV(params, b, fenv) => if (args.length != params.length) error("wrong arity") else 
          interp(TupleE(args), env, _ match {
            case TupleV(argv) => interp(b, fenv ++ (params zip argv).toMap, k, hr)
            case v => k(v)
          }, hr)
        case ContV(kv) => if (args.length != 1) error("there must be exactly one argument to apply continuation") else interp(args(0), env, kv(_), hr)
        case v => interp(TupleE(args), env, _ match {
            case TupleV(argv) => error(s"neither closure nor continuation: $v")
            case av => k(av)
          }, hr)
      })
    case Test(e, typ) => interp(e, env, (_, typ) match {
      case (IntV(_), IntT) | (BooleanV(_), BooleanT) | (TupleV(_), TupleT) | (NilV, ListT) | (ConsV(_,_), ListT) | (CloV(_,_,_), FunctionT) | (ContV(_), FunctionT) => k(BooleanV(true))
      case (_, _) => k(BooleanV(false))
    }, hr)
    case Throw(e) => hr match {
      case None => error("no exception handler")
      case Some(Handler(eh, envh, kh, ph)) => interp(e, env, v => interp(eh, envh, _ match {
        case CloV(params, b, fenv) => if (params.length != 1) error("must have exactly one parameter") else interp(b, fenv + (params(0)->v), kh, ph)
        case ContV(kv) => kv(v)
        case hv => error(s"neither closure nor continuation: $hv")
      }, ph), hr)
    }
    case Try(e, he) => interp(e, env, k, Some(Handler(he, env, k, hr)))
  }

  def interp(expr: Expr): Value = interp(expr, Map(), x => x, None)

}
