// multi-level core language λ↑↓ as a definitional interpreter in Scala

object Base {
  var log: Val => Unit = {x => println(x)}

  // expressions
  abstract class Exp
  case class Lit(n:Int) extends Exp
  case class Sym(s:String) extends Exp
  case class Var(n:Int) extends Exp
  case class App(e1:Exp, e2:Exp) extends Exp
  case class Lam(e:Exp) extends Exp
  case class Let(e1:Exp,e2:Exp) extends Exp
  case class If(c:Exp,a:Exp,b:Exp) extends Exp
  case class Plus(a:Exp,b:Exp) extends Exp
  case class Minus(a:Exp,b:Exp) extends Exp
  case class Times(a:Exp,b:Exp) extends Exp
  case class Equ(a:Exp,b:Exp) extends Exp
  case class Cons(a:Exp,b:Exp) extends Exp
  case class Fst(a:Exp) extends Exp
  case class Snd(a:Exp) extends Exp
  case class IsNum(a:Exp) extends Exp
  case class IsStr(a:Exp) extends Exp
  case class IsCons(a:Exp) extends Exp
  case class Lift(e:Exp) extends Exp
  case class Run(b:Exp,e:Exp) extends Exp
  case class Log(b:Exp,e:Exp) extends Exp

  // for custom extensions to AST
  case class Special(f:Env => Val) extends Exp {
    override def toString = "<special>"
  }

  // values
  type Env = List[Val]

  abstract class Val
  case class Cst(n:Int) extends Val
  case class Str(s:String) extends Val
  case class Clo(env:Env,e:Exp) extends Val
  case class Tup(v1:Val,v2:Val) extends Val

  case class Code(e:Exp) extends Val

  // interpreter state and mechanics
  var stFresh = 0
  var stBlock: List[Exp] = Nil
  var stFun: List[(Int,Env,Exp)] = Nil
  def run[A](f: => A): A = {
    val sF = stFresh
    val sB = stBlock
    val sN = stFun
    try f finally { stFresh = sF; stBlock = sB; stFun = sN }
  }

  def fresh() = {
    stFresh += 1; Var(stFresh-1)
  }
  def reify(f: => Exp) = run {
    stBlock = Nil
    val last = f
    (stBlock foldRight last)(Let)
  }
  def reflect(s:Exp) = {
    stBlock :+= s
    fresh()
  }

  // anf conversion: for checking generated against expected code
  def anf(env: List[Exp], e: Exp): Exp = e match {
    case Lit(n) => Lit(n)
    case Sym(n) => Sym(n)
    case Var(n) => env(n)
    case App(e1,e2) =>
      reflect(App(anf(env,e1),anf(env,e2)))
    case Lam(e) => 
      reflect(Lam(reify(anf(env:+fresh():+fresh(),e))))
    case Let(e1,e2) => 
      anf(env:+(anf(env,e1)),e2)
    case If(c,a,b) => 
      reflect(If(anf(env,c),reify(anf(env,a)),reify(anf(env,b))))
    case Plus(e1,e2) =>
      reflect(Plus(anf(env,e1),anf(env,e2)))
    case Times(e1,e2) =>
      reflect(Times(anf(env,e1),anf(env,e2)))
    case Minus(e1,e2) =>
      reflect(Minus(anf(env,e1),anf(env,e2)))
    case Equ(e1,e2) =>
      reflect(Equ(anf(env,e1),anf(env,e2)))
    case Cons(e1,e2) =>
      reflect(Cons(anf(env,e1),anf(env,e2)))
    case IsNum(e) =>
      reflect(IsNum(anf(env,e)))
    case IsStr(e) =>
      reflect(IsStr(anf(env,e)))
    case IsCons(e) =>
      reflect(IsCons(anf(env,e)))
    case Fst(e) =>
      reflect(Fst(anf(env,e)))
    case Snd(e) =>
      reflect(Snd(anf(env,e)))
    case Lift(e) =>
      reflect(Lift(anf(env,e)))
    case Run(b,e) =>
      reflect(Run(anf(env,b),reify(anf(env,e))))
    case Log(b,e) =>
      reflect(Log(anf(env,b),reify(anf(env,e))))
    case Special(f) =>
      reflect(Special(f))
  }


  def reifyc(f: => Val) = reify { val Code(e) = f; e }
  def reflectc(s: Exp) = Code(reflect(s))

  def reifyv(f: => Val) = run {
    stBlock = Nil
    val res = f
    if (stBlock != Nil) {
      // if we are generating code at all,
      // the result must be code
      val Code(last) = res
      Code((stBlock foldRight last)(Let))
    } else {
      res
    }
  }

  // NBE-style 'reify' operator (semantics -> syntax)
  // lifting is shallow, i.e. 
  //   Rep[A]=>Rep[B]  ==> Rep[A=>B]
  //   (Rep[A],Rep[B]) ==> Rep[(A,B)]
  def lift(v: Val): Exp = v match {
    case Cst(n) => // number
      Lit(n)
    case Str(s) => // string
      Sym(s)
    case Tup(a,b) =>
      val (Code(u),Code(v)) = (a,b)
      reflect(Cons(u,v))
    case Clo(env2,e2) => // function
      // NOTE: We memoize functions here. This is not essential, and 
      // could be removed, yielding exactly the code shown in the paper.
      stFun collectFirst { case (n,`env2`,`e2`) => n } match {
        case Some(n) =>
          Var(n)
        case None =>
          stFun :+= (stFresh,env2,e2)
          reflect(Lam(reify{ val Code(r) = evalms(env2:+Code(fresh()):+Code(fresh()),e2); r }))
      }
    case Code(e) => reflect(Lift(e))
  }

  // multi-stage evaluation
  def evalms(env: Env, e: Exp): Val = e match {
    case Lit(n) => Cst(n)
    case Sym(s) => Str(s)
    case Var(n) => env(n)
    case Lam(e) => Clo(env,e)
    case Let(e1,e2) => 
      val v1 = evalms(env,e1)
      evalms(env:+v1,e2)

    case Lift(e) => 
      Code(lift(evalms(env,e)))

    case Run(b,e) =>
      // first argument decides whether to generate
      // `run` statement or run code directly
      evalms(env,b) match {
        case Code(b1) =>
          reflectc(Run(b1, reifyc(evalms(env,e))))
        case _ =>
          val code = reifyc({ stFresh = env.length; evalms(env, e) })
          reifyv(evalms(env, code))
      }

    case Log(b,e) =>
      evalms(env,b) match {
        case Code(b1) =>
          reflectc(Log(b1, reifyc(evalms(env,e))))
        case _ =>
          val r = evalms(env, e)
          log(r)
          r
      }

    case App(e1,e2) =>
      (evalms(env,e1), evalms(env,e2)) match {
        case (Clo(env3,e3), v2) => 
          evalms(env3:+Clo(env3,e3):+v2,e3)
        case (Code(s1), Code(s2)) =>
          Code(reflect(App(s1,s2)))
        case (r1, r2) =>
          val r2s = r2 match {
            case Clo(_, _) => r2.getClass.toString
            case _ => r2.toString
          }
          throw new Exception(s"wrong app: ${r1.toString} $r2s")
      }

    case If(c,a,b) =>
      evalms(env,c) match {
        case Cst(n) => 
          if (n != 0) evalms(env,a) else evalms(env,b)
        case (Code(c1)) =>
          reflectc(If(c1, reifyc(evalms(env,a)), reifyc(evalms(env,b))))
      }

    case Plus(e1,e2) =>
      (evalms(env,e1), evalms(env,e2)) match {
        case (Cst(n1), Cst(n2)) =>
          Cst(n1+n2)
        case (Code(s1),Code(s2)) =>
          reflectc(Plus(s1,s2))
      }
    case Minus(e1,e2) =>
      (evalms(env,e1), evalms(env,e2)) match {
        case (Cst(n1), Cst(n2)) =>
          Cst(n1-n2)
        case (Code(s1),Code(s2)) =>
          reflectc(Minus(s1,s2))
      }
    case Times(e1,e2) =>
      (evalms(env,e1), evalms(env,e2)) match {
        case (Cst(n1), Cst(n2)) =>
          Cst(n1*n2)
        case (Code(s1),Code(s2)) =>
          reflectc(Times(s1,s2))
      }
    case Equ(e1,e2) =>
      (evalms(env,e1), evalms(env,e2)) match {
        case (v1, v2) if !v1.isInstanceOf[Code] && !v2.isInstanceOf[Code] =>
          Cst(if (v1 == v2) 1 else 0)
        case (Code(s1),Code(s2)) =>
          reflectc(Equ(s1,s2))
      }
    case Cons(e1,e2) =>
      // introduction form, needs explicit lifting
      // (i.e. don't match on args)
      Tup(evalms(env,e1),evalms(env,e2))
    case Fst(e1) =>
      (evalms(env,e1)) match {
        case (Tup(a,b)) => 
          a
        case (Code(s1)) =>
          Code(reflect(Fst(s1)))
      }
    case Snd(e1) =>
      (evalms(env,e1)) match {
        case (Tup(a,b)) => 
          b
        case (Code(s1)) =>
          Code(reflect(Snd(s1)))
      }
    case IsNum(e1) =>
      (evalms(env,e1)) match {
        case (Code(s1)) =>
          Code(reflect(IsNum(s1)))
        case v => 
          Cst(if (v.isInstanceOf[Cst]) 1 else 0)
      }
    case IsStr(e1) =>
      (evalms(env,e1)) match {
        case (Code(s1)) =>
          Code(reflect(IsStr(s1)))
        case v => 
          Cst(if (v.isInstanceOf[Str]) 1 else 0)
      }

    case IsCons(e1) =>
      (evalms(env,e1)) match {
        case (Code(s1)) =>
          Code(reflect(IsCons(s1)))
        case v => 
          Cst(if (v.isInstanceOf[Tup]) 1 else 0)
      }

    // special forms: custom eval, ...
    case Special(f) => f(env)
  }


  // pretty printing
  var indent = "\n"
  def block(a: => String): String = {
    val save = indent
    indent += "  "
    try a finally indent = save
  }
  def pretty(e: Exp, env: List[String]): String = e match {
    case Lit(n)     => n.toString
    case Sym(n)     => "'"+n
    case Var(x)     => try env(x) catch { case _ => "?" }
    case IsNum(a)   => s"(num? ${pretty(a,env)})"
    case IsStr(a)   => s"(sym? ${pretty(a,env)})"
    case Lift(a)    => s"(lift ${pretty(a,env)})"
    case Fst(a)     => s"(car ${pretty(a,env)})"
    case Snd(a)     => s"(cdr ${pretty(a,env)})"
    case Cons(a,b)  => s"(cons ${pretty(a,env)} ${pretty(b,env)})"
    case Equ(a,b)   => s"(eq? ${pretty(a,env)} ${pretty(b,env)})"
    case Plus(a,b)  => s"(+ ${pretty(a,env)} ${pretty(b,env)})"
    case Minus(a,b) => s"(- ${pretty(a,env)} ${pretty(b,env)})"
    case Times(a,b) => s"(* ${pretty(a,env)} ${pretty(b,env)})"
    case Run(a,b)   => s"(run ${pretty(a,env)} ${pretty(b,env)})"
    case Log(a,b)   => s"(log ${pretty(a,env)} ${pretty(b,env)})"
    case App(a,b)   => s"(${pretty(a,env)} ${pretty(b,env)})"
    case Let(a,Var(n)) if n == env.length => pretty(a,env)
    case Let(a,b)   => s"${indent}(let x${env.length} ${block(pretty(a,env))} ${(pretty(b,env:+("x"+env.length)))})"
    case Lam(e)     => s"${indent}(lambda f${env.length} x${env.length+1} ${block(pretty(e,env:+("f"+env.length):+("x"+(env.length+1))))})"
    case If(c,a,b)  => s"${indent}(if ${pretty(c,env)} ${block(pretty(a,env))} ${indent}${block(pretty(b,env))})"
    case _          => e.toString
  }

  var testsRun = 0
  def testDone(): Unit = {
    println(s"  Tests run: $testsRun"); testsRun = 0
  }

  def check(a:Any)(s:String) = if (a.toString.trim != s.trim) {
    println("error: expected ")
    println("    "+s)
    println("but got")
    println("    "+a)
    (new AssertionError).printStackTrace
  } else testsRun += 1


  // basic test cases
  def test() = {
    println("// ------- Base.test --------")
    println("Staged factorial...")
/*
  pattern:
    def f = fun { n => if (n != 0) f(n-1) else 1 }
  corresponds to:
    val f = { () => lift({ n => if (n != 0) f()(n-1) else 1 }) }

*/
    val f_self = App(Var(0),Lit(99))
    val n = Var(3)

    val fac_body = Lam(If(n,Times(n,App(f_self,Minus(n,Lift(Lit(1))))),Lift(Lit(1))))
    val fac = App(Lam(Lift(fac_body)),Lit(99))
    val code = reifyc(evalms(Nil,fac))
    val out = 
      Let(Lam(
        Let(If(Var(1),
              Let(Minus(Var(1),Lit(1)),
              Let(App(Var(0),Var(2)),
              Let(Times(Var(1),Var(3)),
              Var(4)))),
            /* else */
              Lit(1)
        ),
        Var(2))),
      Var(0))

    check(code)(out.toString)

    check(evalms(Nil,App(code,Lit(4))))("Cst(24)")

    testDone()
  }


}
