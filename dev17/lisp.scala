object Lisp {
  import Base._

  import scala.util.parsing.combinator._

  // from github.com/namin/lms-black
  object parser extends JavaTokenParsers with PackratParsers {
    override val whiteSpace = """(\s|(;[^\n]*))+""".r

    def S(x:String) = Str(x)
    def Str2(x:String) = ???
    def P(x:Val,y:Val) = Tup(x,y)
    def B(x:Boolean) = ???
    def I(x:Int) = Cst(x)
    val N = Str(".")

    lazy val exp: Parser[Val] =
        "#f" ^^ { case _ => B(false) } |
        "#t" ^^ { case _ => B(true) } |
        wholeNumber ^^ { case s => I(s.toInt) } |
        """[^\s\(\)'"]+""".r ^^ { case s => S(s) } |
        stringLiteral ^^ { case s => Str2(s.substring(1, s.length-1)) } |
        "'" ~> exp ^^ { case s => P(S("quote"), P(s, N)) } |
        "()" ^^ { case _ => N } |
        "(" ~> exps <~ ")" ^^ { case vs => vs }

    lazy val exps: Parser[Val] =
        exp ~ opt(exps) ^^ { case v~Some(vs) => P(v, vs) case v~None => P(v,N) }
  }


  import parser._

  /* 
    alternative: use right-to-left de brujin indexes to make closures ctx-independent
    (not so simple b/c let insertion)
  */

  // ********************* convert exp encoded as val --> exp  *********************

  var traceExec = false
  def trans(e: Val, env: List[String]): Exp = e match {
    case Cst(n) => Lit(n)
    case Str(s) => val i = env.lastIndexOf(s); assert(i>=0, s + " not in " + env); Var(i)
    case Tup(Str("quote"),Tup(Str(s),N)) => Sym(s)
    case Tup(Str("+"),Tup(a,Tup(b,N))) => Plus(trans(a,env),trans(b,env))
    case Tup(Str("-"),Tup(a,Tup(b,N))) => Minus(trans(a,env),trans(b,env))
    case Tup(Str("*"),Tup(a,Tup(b,N))) => Times(trans(a,env),trans(b,env))
    // (let x a b)
    case Tup(Str("let"),Tup(Str(x),Tup(a,Tup(b,N)))) => Let(trans(a,env),trans(b,env:+x))
    // (lambda f x e)
    case Tup(Str("lambda"),Tup(Str(f),Tup(Str(x),Tup(e,N)))) => Lam(trans(e,env:+f:+x))
    case Tup(Str("if"),Tup(c,Tup(a,Tup(b,N)))) => If(trans(c,env),trans(a,env),trans(b,env))
    case Tup(Str("isNum"),Tup(a,N)) => IsNum(trans(a,env))
    case Tup(Str("isStr"),Tup(a,N)) => IsStr(trans(a,env))
    case Tup(Str("isPair"),Tup(a,N)) => IsPair(trans(a,env))
    case Tup(Str("isCode"),Tup(a,Tup(b,N))) => IsCode(trans(a,env),trans(b,env))
    case Tup(Str("cons"),Tup(a,Tup(b,N))) => Pair(trans(a,env),trans(b,env))
    case Tup(Str("car"),Tup(a,N)) => Fst(trans(a,env))
    case Tup(Str("cdr"),Tup(a,N)) => Snd(trans(a,env))
    case Tup(Str("lift"),Tup(a,N)) => Lift(trans(a,env))
    case Tup(Str("nolift"),Tup(a,N)) => trans(a,env)
    case Tup(Str("equs"),Tup(a,Tup(b,N))) => Equs(trans(a,env),trans(b,env))
    // mutable refs
    case Tup(Str("lift-ref"),Tup(a,N)) => Special(benv => Code(Special(b2 => evalms(benv,trans(a,env))))) //LiftRef(trans(a,env))
    case Tup(Str("nolift-ref"),Tup(a,N)) => trans(a,env)
    case Tup(Str("refNew"),Tup(a,N)) => RefNew(trans(a,env))
    case Tup(Str("refRead"),Tup(a,N)) => RefRead(trans(a,env))
    case Tup(Str("refWrite"),Tup(a,Tup(e,N))) => RefWrite(trans(a,env),trans(e,env))
    case Tup(Str("log"),Tup(a,N)) => def log(e: Exp): Special = Special{benv => evalms(benv,e) match {
      case Code(e) => reflectc(log(e))
      case v => println(v.toString); v
    }}
    log(trans(a,env))
    // special forms: eval / trans assume empty env for now
    case Tup(Str("exec"),Tup(a,N)) => 
      def trace(x:Exp): Exp = { if (traceExec) println(">>> compile: " + pretty(x,Nil)); x }
      Special(benv => evalms(Nil, trace(reifyc(evalms(benv, trans(a,env))))))
    case Tup(Str("exec"),Tup(b,Tup(a,N))) =>
      // Note: the only difference with Eval is that we use Nil instead of benv below
      //   for second run.
      def trace(x:Exp): Exp = { if (traceExec) println(">>> compile: " + pretty(x,Nil)); x }
      def f(b: Exp, a: Exp): Special = Special(benv =>
        evalms(benv, b) match {
          case Code(b1) => reflectc(f(b1, reifyc(evalms(benv,a))))
          case _ => evalms(Nil, trace(reifyc(evalms(benv, a))))
        })
      f(trans(b, env), trans(a, env))
    case Tup(Str("trans-quote"),Tup(a,N)) =>
      Special(benv => Code(trans(evalms(benv, trans(a,env)), Nil)))
    // but EM needs a version that uses current env
    case Tup(Str("exec/env"),Tup(b,Tup(a,N))) => 
      //Special(benv => evalms(benv, reifyc(evalms(benv, trans(a,env)))))
      Eval(trans(b,env),trans(a,env))
    case Tup(Str("trans-quote/env"),Tup(a,N)) => 
      Special(benv => Code(trans(evalms(benv, trans(a,env)), env)))
    case Tup(Str("quote"),Tup(a,N)) => Special(benv => a)
    // default case: generic app
    case Tup(a,Tup(b,N)) => App(trans(a,env),trans(b,env))
  }

  // NOTE:
  // here, missing meta-circular implementation of exec, exec/env, trans-quote, trans-quote/env
  // but see Pink.Pink_clambda for how it can be done


  // ********************* source programs  *********************

  val fac_src = "(lambda f n (if n (* n (f (- n 1))) 1))"
  val mut_src = "(let c (refNew 0) (lambda _ n (refRead (refWrite c (- (refRead (refWrite c (+ (refRead c) 28))) n)))))"

  val eval_poly_src = """
  (lambda eval exp (lambda _ env
    (if (isNum               exp)       (maybe-lift exp)
    (if (isStr               exp)       (env exp)
    (if (isStr          (car exp))      
      (if (equs '+      (car exp))      (+  ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      (if (equs '-      (car exp))      (-  ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      (if (equs '*      (car exp))      (*  ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      (if (equs 'equs   (car exp))      (equs ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      (if (equs 'if     (car exp))      (if ((eval (cadr exp)) env) ((eval (caddr exp)) env) ((eval (cadddr exp)) env))
      (if (equs 'lambda (car exp))      (maybe-lift (lambda f x ((eval (cadddr exp)) (lambda _ y (if (equs y (cadr exp)) f (if (equs y (caddr exp)) x (env y)))))))
      (if (equs 'let    (car exp))      (let x ((eval (caddr exp)) env) ((eval (cadddr exp)) (lambda _ y (if (equs y (cadr exp)) x (env y)))))
      (if (equs 'lift       (car exp))      (lift       ((eval (cadr exp)) env))
      (if (equs 'lift-ref   (car exp))      (lift-ref   ((eval (cadr exp)) env))
      (if (equs 'nolift     (car exp))      (nolift     ((eval (cadr exp)) env))
      (if (equs 'nolift-ref (car exp))      (nolift-ref ((eval (cadr exp)) env))
      (if (equs 'isNum  (car exp))      (isNum ((eval (cadr exp)) env))
      (if (equs 'isStr  (car exp))      (isStr ((eval (cadr exp)) env))
      (if (equs 'cons   (car exp))      (maybe-lift (cons ((eval (cadr exp)) env) ((eval (caddr exp)) env)))
      (if (equs 'car    (car exp))      (car ((eval (cadr exp)) env))
      (if (equs 'cdr    (car exp))      (cdr ((eval (cadr exp)) env))
      (if (equs 'quote  (car exp))      (maybe-lift (cadr exp))
      (if (equs 'EM     (car exp))      'em-not-supported
      (if (equs 'exec/env (car exp))    (exec/env ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      (if (equs 'refNew (car exp))      (maybe-lift (refNew ((eval (cadr exp)) env)))
      (if (equs 'refRead (car exp))     (refRead ((eval (cadr exp)) env))
      (if (equs 'refWrite (car exp))    (refWrite ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      ((env (car exp)) ((eval (cadr exp)) env))))))))))))))))))))))))
    (((eval (car exp)) env) ((eval (cadr exp)) env))
    )))))""".
    replace("(cadr exp)","(car (cdr exp))").
    replace("(caddr exp)","(car (cdr (cdr exp)))").
    replace("(cadddr exp)","(car (cdr (cdr (cdr exp))))")

  val eval_cps_poly_src = """
  (lambda eval exp (lambda _ env (lambda _ k
    (if (isNum               exp)       (k (maybe-lift exp))
    (if (isStr               exp)       (k (env exp))
    (if (isStr          (car exp))
      (if (equs '+      (car exp))      (((eval (cadr exp)) env) (lambda _ v1 (((eval (caddr exp)) env) (lambda _ v2 (k (+ v1 v2))))))
      (if (equs '-      (car exp))      (((eval (cadr exp)) env) (lambda _ v1 (((eval (caddr exp)) env) (lambda _ v2 (k (- v1 v2))))))
      (if (equs '*      (car exp))      (((eval (cadr exp)) env) (lambda _ v1 (((eval (caddr exp)) env) (lambda _ v2 (k (* v1 v2))))))
      (if (equs 'equs   (car exp))      (((eval (cadr exp)) env) (lambda _ v1 (((eval (caddr exp)) env) (lambda _ v2 (k (equs v1 v2))))))
      (if (equs 'if     (car exp))      (((eval (cadr exp)) env) (lambda _ vc (if vc (((eval (caddr exp)) env) k) (((eval (cadddr exp)) env) k))))
      (if (equs 'lambda (car exp))           (k (maybe-lift (lambda f x (maybe-lift ((eval (cadddr exp)) (lambda _ y (if (equs y (cadr exp)) f (if (equs y (caddr exp)) x (env y)))))))))
      (if (equs 'let    (car exp))      (((eval (caddr exp)) env) (maybe-lift (lambda _ v (let x v (((eval (cadddr exp)) (lambda _ y (if (equs y (cadr exp)) x (env y)))) k)))))
      (if (equs 'lift   (car exp))      (((eval (cadr exp)) env) (lambda _ v (k (lift v))))
      (if (equs 'nolift (car exp))      (((eval (cadr exp)) env) (lambda _ v (k (nolift v))))
      (if (equs 'isNum  (car exp))      (((eval (cadr exp)) env) (lambda _ v (k (isNum v))))
      (if (equs 'isStr  (car exp))      (((eval (cadr exp)) env) (lambda _ v (k (isStr v))))
      (if (equs 'cons   (car exp))      (((eval (cadr exp)) env) (lambda _ v1 (((eval (caddr exp)) env) (lambda _ v2 (k (maybe-lift (cons v1 v2)))))))
      (if (equs 'car    (car exp))      (((eval (cadr exp)) env) (lambda _ v (k (car v))))
      (if (equs 'cdr    (car exp))      (((eval (cadr exp)) env) (lambda _ v (k (cdr v))))
      (if (equs 'call/cc (car exp))     ((((eval (cadr exp)) env) (nolift (lambda _ p (p (maybe-lift (lambda _ v (maybe-lift (lambda _ k1 (k v)))))))))  (maybe-lift (lambda _ v (k v))))
      (if (equs 'quote  (car exp))      (k (maybe-lift (cadr exp)))
      (if (equs 'begin (car exp))
          (if (if (isStr (cdr exp)) (equs '. (cdr exp)) 0) (k (maybe-lift 'done))
          (if (if (isStr (cdr (cdr exp))) (equs '. (cdr (cdr exp))) 0) (((eval (cadr exp)) env) k)
          (((eval (cadr exp)) env) (lambda _ _ (((eval (cons 'begin (cdr (cdr exp)))) env) k)))))
      (if (equs 'amb (car exp))

(((eval (cons 'let (cons 'prev-amb-fail (cons '(refRead amb-fail) (cons

(cons 'call/cc (cons (cons 'lambda (cons '_ (cons 'sk
(cons (cons 'begin
(((lambda map f (lambda _ xs (if (if (isStr xs) (equs '. xs) 0)
(cons '(prev-amb-fail 1) '.)
(cons (f (car xs)) ((map f) (cdr xs))))))
 (lambda _ alt (cons 'call/cc (cons (cons 'lambda (cons '_ (cons 'fk (cons (cons 'begin
   (cons (cons 'refWrite (cons 'amb-fail
(cons (cons 'lambda (cons '_ (cons '_ (cons (cons 'begin (cons '(refWrite amb-fail prev-amb-fail) (cons (cons 'fk (cons 0 '.)) '.))) '.)))) '.)))
   (cons (cons 'sk (cons alt '.)) '.))) '.)))) '.)))) (cdr exp)))'.)
))) '.))


'.)))) ) env) k)

      (if (equs 'refNew (car exp))      (((eval (cadr exp)) env) (lambda _ v (k (maybe-lift (refNew v)))))
      (if (equs 'refRead (car exp))     (((eval (cadr exp)) env) (lambda _ v (k (refRead v))))
      (if (equs 'refWrite (car exp))    (((eval (cadr exp)) env) (lambda _ v1 (((eval (caddr exp)) env) (lambda _ v2 (k (refWrite v1 v2))))))
      (if (equs 'EM     (car exp))      'em-not-supported
      (((eval (cadr exp)) env) (nolift (lambda _ v (((env (car exp)) v) (maybe-lift (lambda _ x (k x))) ))))))))))))))))))))))))))
    (((eval (car exp)) env) (nolift (lambda _ v1 (((eval (cadr exp)) env) (nolift (lambda _ v2 ((v1 v2) (maybe-lift (lambda _ x (k x))) )))))))
    ))))))""".
    replace("(cadr exp)","(car (cdr exp))").
    replace("(caddr exp)","(car (cdr (cdr exp)))").
    replace("(cadddr exp)","(car (cdr (cdr (cdr exp))))")

  val eval_vc_poly_src = s"""(lambda _ c
${eval_poly_src.replace("(env exp)", "(let _ (if (equs 'n exp) (refWrite c (+ (refRead c) (trace-lift 1))) (trace-lift 0)) (env exp))")}
)
"""

  // so far, we support only one level of EM
  val eval_em_poly_src = eval_poly_src.replace("'em-not-supported","(exec/env 0 (trans-quote/env (car (cdr exp))))")
  val eval_em_cps_poly_src = eval_cps_poly_src.replace("'em-not-supported","(exec/env 0 (trans-quote/env (car (cdr exp))))")

  val eval_src = eval_poly_src.replace("maybe-lift","nolift") // plain interpreter
  val evalc_src = eval_poly_src.replace("maybe-lift","lift")  // generating extension = compiler

  val eval_vc_src = eval_vc_poly_src.replace("trace-lift","nolift").replace("maybe-lift","nolift") // plain interpreter
  val evalc_vc_src = eval_vc_poly_src.replace("trace-lift","lift").replace("maybe-lift","lift")  // generating extension = compiler

  val evalt_vc_src = eval_vc_poly_src.replace("trace-lift","lift").replace("maybe-lift","nolift")  // transformer


  val eval_cps_src = eval_cps_poly_src.replace("maybe-lift","nolift") // plain interpreter
  val evalc_cps_src = eval_cps_poly_src.replace("maybe-lift","lift")  // generating extension = compiler

  // next step (see Pink): take maybe-lift as parameter instead of simulating macros

  // NOTE: have to be careful with 'equs': if arg is not a string, it might create a code object */

  def parseExp(s: String) = {
    val Success(v, _) = parseAll(exp, s)
    v
  }

  val fac_val = parseExp(fac_src)
  val mut_val = parseExp(mut_src)
  val eval_val = parseExp(eval_src)
  val evalc_val = parseExp(evalc_src)
  val eval_vc_val = parseExp(eval_vc_src)
  val evalc_vc_val = parseExp(evalc_vc_src)
  val evalt_vc_val = parseExp(evalt_vc_src)
  val eval_cps_val = parseExp(eval_cps_src)
  val evalc_cps_val = parseExp(evalc_cps_src)

  val fac_exp = trans(fac_val,List("arg"))
  val mut_exp = trans(mut_val,List("arg"))
  val eval_exp = trans(eval_val,List("arg","arg2"))
  val evalc_exp = trans(evalc_val,List("arg","arg2"))
  val eval_vc_exp = trans(eval_vc_val,List("arg","arg2", "arg3"))
  val evalc_vc_exp = trans(evalc_vc_val,List("arg","arg2", "arg3"))
  val evalt_vc_exp = trans(evalt_vc_val,List("arg","arg2", "arg3"))
  val eval_cps_exp = trans(eval_cps_val,List("arg","arg2"))
  val evalc_cps_exp = trans(evalc_cps_val,List("arg","arg2"))

  val fac_exp_anf = reify { anf(List(Sym("XX")),fac_exp) }
  val mut_exp_anf = reify { anf(List(Sym("XX")),mut_exp) }
  val eval_exp_anf = reify { anf(List(Sym("XX"),Sym("XX")),eval_exp) }
  val evalc_exp_anf = reify { anf(List(Sym("XX"),Sym("XX")),evalc_exp) }
  val eval_vc_exp_anf = reify { anf(List(Sym("XX"),Sym("XX"),Sym("XX")),eval_vc_exp) }
  val evalc_vc_exp_anf = reify { anf(List(Sym("XX"),Sym("XX"),Sym("XX")),evalc_vc_exp) }
  val evalt_vc_exp_anf = reify { anf(List(Sym("XX"),Sym("XX"),Sym("XX")),evalt_vc_exp) }
  val eval_cps_exp_anf = reify { anf(List(Sym("XX"),Sym("XX")),eval_cps_exp) }
  val evalc_cps_exp_anf = reify { anf(List(Sym("XX"),Sym("XX")),evalc_cps_exp) }

  // ********************* test cases *********************

  def testEval() = {
    println("// ------- test eval --------")

    check(fac_exp_anf)("Let(Lam(Let(If(Var(1),Let(Minus(Var(1),Lit(1)),Let(App(Var(0),Var(2)),Let(Times(Var(1),Var(3)),Var(4)))),Lit(1)),Var(2))),Var(0))")


    // -----------------------------------------------
    // interpretation

    val r1 = run { evalms(List(fac_val,eval_val),App(App(App(eval_exp,Var(0)),Sym("nil-env")),Lit(4))) }

    check(r1)("Cst(24)")


    // generation + interpretation

    val c1 = reifyc { evalms(List(fac_val,eval_val),App(App(evalc_exp,Var(0)),Sym("nil-env"))) }

    check(c1)(fac_exp_anf.toString)

    val r2 = run { evalms(Nil,App(c1,Lit(4))) }

    check(r2)("Cst(24)")

    // we can show:
    // (evalms (evalc fac)) = fac
    // (evalms (evalc eval)) = eval
    // (evalms (evalc evalc)) = evalc



    // -----------------------------------------------
    // double interpretation!!

    // first try a plain value ... (evalms ((eval eval) 24)) = 24
    val r3 = run { evalms(List(fac_val,eval_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Lit(24)), Sym("nil-env2"))) }

    check(r3)("Cst(24)")


    // double eval fac ... (evalms (((eval eval) fac) 4)) = 24
    val r4 = run { evalms(List(fac_val,eval_val), App(App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2")), Lit(4))) }

    check(r4)("Cst(24)")


    // code generation through double interpretation !!!  (evalms ((eval evalc) fac)) = fac

    val c2 = reifyc { evalms(List(fac_val,evalc_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2"))) }

    check(c2)(fac_exp_anf.toString)

    val r5 = run { evalms(Nil,App(c2,Lit(4))) }

    check(r5)("Cst(24)")



    // now generate evaluator ... (evalms ((eval evalc) eval)) = eval

    val c3 = reifyc { evalms(List(eval_val,evalc_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2"))) }

    // this is our evaluator!!!  
    // println("--- decompiled eval ---")
    // println(pretty(c3,Nil)) 
    //check(c3)(eval_exp_anf.toString)
    check(pretty(c3,Nil))(pretty(eval_exp_anf,Nil).toString) // compare prettyprinted b/c extra let

    // test that we can use the evaluator to run fac
    // NOTE: cannot put fac_val intro env!! 
    val r6 = run { val eval_val3 = evalms(Nil,c3); evalms(List(eval_val3,fac_val),App(App(App(Var(0),Var(1)), Sym("nil-env")), Lit(4))) }

    check(r6)("Cst(24)")



    // now generate generator ... (evalms ((eval evalc) evalc)) = evalc

    val c4 = reifyc { evalms(List(eval_val,evalc_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(1)), Sym("nil-env2"))) }

    // this is our generator!!!
    // println("--- decompiled evalc ---")
    // println(pretty(c4,Nil))
    //check(c4)(evalc_exp_anf.toString)
    check(pretty(c4,Nil))(pretty(evalc_exp_anf,Nil).toString) // compare prettyprinted b/c extra let

    val c5 = reifyc { val eval_valc4 = evalms(Nil,c4); evalms(List(eval_valc4,fac_val),App(App(Var(0),Var(1)), Sym("nil-env"))) }


    // this is fac, generated by decompiled evalc
    // println("--- fac generated by decompiled evalc ---")
    // println(pretty(c5,Nil)) 
    check(c5)(fac_exp_anf.toString)

    val r7 = run { evalms(Nil,App(c5,Lit(4))) }

    check(r7)("Cst(24)")

    // we have:
    // (evalms ((eval evalc) fac)) = fac
    // (evalms ((eval evalc) eval) = eval
    // (evalms ((eval evalc) evalc) = evalc


    // -----------------------------------------------
    // triple interpretation!!

    val eval_exp3 = trans(eval_val,List("arg","arg2","arg3")) // need three slots in env...

    // triple eval fac ... (evalms (((eval eval) evalc) fac)) = fac
    val c6 = reifyc { evalms(List(evalc_val,eval_val,fac_val), 
      App(App(App(App(App(App(App(App(eval_exp3,Var(1)),Sym("nil-env")), Var(1)), Sym("nil-env2")), Var(0)), Sym("nil-env3")), Var(2)), Sym("nil-env4"))) }

    check(c6)(fac_exp_anf.toString)
  }

  def testEvalCps(): Unit = {
    println("// ------- test eval CPS --------")

    // -----------------------------------------------
    // interpretation

    val r1 = run { evalms(List(fac_val,eval_cps_val), App(App(App(eval_cps_exp,Var(0)),Sym("nil-env")),Lam(App(App(Var(3),Lit(4)),Lam(Var(5)))))) }
    check(r1)("Cst(24)")

    // generation + interpretation (small checks)

    val p11 = parseExp("(lambda f x (+ x 1))")
    val c11 = reifyc { evalms(List(p11,Cst(1)),App(App(App(evalc_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(pretty(c11, List()))("""
    |fun f0 x1 
    |  fun f2 x3 
    |    let x4 = (x1 + 1) in (x3 x4)
    """.stripMargin) // note: reusing the caller continuation

    val p12 = parseExp("(lambda f x (f x))")
    val c12 = reifyc { evalms(List(p12,Cst(1)),App(App(App(evalc_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(pretty(c12, List()))("""
    |fun f0 x1 
    |  fun f2 x3 
    |    let x4 = (f0 x1) in 
    |    let x5 = 
    |      fun f5 x6 (x3 x6) in (x4 x5)
    """.stripMargin) // note: x3 eta-expanded into x5 (naive cps transform)

    val p13 = parseExp("(lambda f x (f (+ x 1)))")
    val c13 = reifyc { evalms(List(p13,Cst(1)),App(App(App(evalc_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(pretty(c13, List()))("""
    |fun f0 x1 
    |  fun f2 x3 
    |    let x4 = (x1 + 1) in 
    |    let x5 = (f0 x4) in 
    |    let x6 = 
    |      fun f6 x7 (x3 x7) in (x5 x6)
    """.stripMargin) // note: x3 eta-expanded into x6 (naive cps transform)

    val p14 = parseExp("(lambda f x (+ 1 (f x)))")
    val c14 = reifyc { evalms(List(p14,Cst(1)),App(App(App(evalc_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(pretty(c14, List()))("""
    |fun f0 x1 
    |  fun f2 x3 
    |    let x4 = (f0 x1) in 
    |    let x5 = 
    |      fun f5 x6 
    |        let x7 = (1 + x6) in (x3 x7) in (x4 x5)
    """.stripMargin)

    val p15 = parseExp("(let f (lambda f x (+ 1 x)) (f 3))")
    val c15 = reifyc { evalms(List(p15,Cst(1)),App(App(App(evalc_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(pretty(c15, List()))("""
    |let x0 = 
    |  fun f0 x1 
    |    let x2 = (x1 3) in 
    |    let x3 = 
    |      fun f3 x4 x4 in (x2 x3) in 
    |let x1 = 
    |  fun f1 x2 
    |    fun f3 x4 
    |      let x5 = (1 + x2) in (x4 x5) in (x0 x1)
    """.stripMargin)



    // generation + interpretation (factorial)

    val c1 = reifyc { evalms(List(fac_val,Cst(1)),App(App(App(evalc_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(pretty(c1, List()))("""
    |fun f0 x1 
    |  fun f2 x3 
    |    if (x1) 
    |      let x4 = (x1 - 1) in 
    |      let x5 = (f0 x4) in 
    |      let x6 = 
    |        fun f6 x7 
    |          let x8 = (x1 * x7) in (x3 x8) in (x5 x6) 
    |    else (x3 1)
    """.stripMargin)

    val r2 = run { evalms(Nil,App(App(c1,Lit(4)),Lam(Var(1)))) }
    check(r2)("Cst(24)")

    // call/cc
    val d3_val = parseExp("(- (call/cc (lambda _ k 2)) 1)")
    val r3 = run { evalms(List(d3_val,Cst(0)), App(App(App(eval_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(r3)("Cst(1)")

    val d4_val = parseExp("(- (call/cc (lambda _ k (* 3 (k 2)))) 1)")
    val r4 = run { evalms(List(d4_val,Cst(0)), App(App(App(eval_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(r4)("Cst(1)")


    // generation

    val c3 = reifyc { evalms(List(d3_val,Cst(0)), App(App(App(evalc_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(pretty(c3, List()))("""
    |let x0 = 
    |  fun f0 x1 
    |    fun f2 x3 (x3 2) in 
    |let x1 = 
    |  fun f1 x2 
    |    fun f3 x4 (x2 - 1) in 
    |let x2 = (x0 x1) in 
    |let x3 = 
    |  fun f3 x4 (x4 - 1) in (x2 x3)
    """.stripMargin)

    val r3a = run { evalms(Nil,c3) }
    check(r3a)("Cst(1)")


    val c4 = reifyc { evalms(List(d4_val,Cst(0)), App(App(App(evalc_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(pretty(c4, List()))("""
    |let x0 = 
    |  fun f0 x1 
    |    fun f2 x3 
    |      let x4 = (x1 2) in 
    |      let x5 = 
    |        fun f5 x6 
    |          let x7 = (3 * x6) in (x3 x7) in (x4 x5) in 
    |let x1 = 
    |  fun f1 x2 
    |    fun f3 x4 (x2 - 1) in 
    |let x2 = (x0 x1) in 
    |let x3 = 
    |  fun f3 x4 (x4 - 1) in (x2 x3)
    """.stripMargin)

    val r4a = run { evalms(Nil,c4) }
    check(r4a)("Cst(1)")



  }

  def testEvalAmb() = {
    println("// ------- test eval CPS AMB --------")

    val b1 = parseExp("(begin 1)")
    val a1 = run { evalms(List(b1,eval_cps_val), App(App(App(eval_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(a1)("Cst(1)")

    val b2 = parseExp("(begin 2)")
    val a2 = run { evalms(List(b2,eval_cps_val), App(App(App(eval_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(a2)("Cst(2)")

    val p1 = parseExp("(let amb-fail (refNew (lambda _ () 'error)) (amb 1))")
    val r1 = run { evalms(List(p1,eval_cps_val), App(App(App(eval_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(r1)("Cst(1)")

    val p2 = parseExp("(let amb-fail (refNew (lambda _ () 'error)) (amb (amb) 1))")
    val r2 = run { evalms(List(p2,eval_cps_val), App(App(App(eval_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(r2)("Cst(1)")

    val p3 = parseExp("(let amb-fail (refNew (lambda _ () 'error)) (if (amb 0 1) 1 (amb)))")
    val r3 = run { evalms(List(p3,eval_cps_val), App(App(App(eval_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(r3)("Cst(1)")

    val p4 = parseExp("(let amb-fail (refNew (lambda _ () 'error)) (let i (amb 1 2 3) (let j (amb 1 2 3) (if (- i j) (amb (+ i j)) (amb)))))")
    val r4 = run { evalms(List(p4,eval_cps_val), App(App(App(eval_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    check(r4)("Cst(3)")

    val p5 = parseExp("(lambda _ x (let amb-fail (refNew (lambda _ () 'error)) (let i (amb x 2 3) (let j (amb 1 2 3) (if (- i j) (amb (+ i j)) (amb))))))")
    val r5 = run { evalms(List(p5,eval_cps_val), App(App(App(eval_cps_exp,Var(0)),Sym("nil-env")),Lam(App(App(Var(3),Lit(1)),Lam(Var(5)))))) }
    check(r5)("Cst(3)")

    val c5 = reifyc { evalms(List(p5,evalc_cps_val), App(App(App(evalc_cps_exp,Var(0)),Sym("nil-env")),Lam(Var(3)))) }
    println(pretty(c5, Nil))
  }

  def testMutEval() = {
    println("// ------- test mutation eval --------")

    // -----------------------------------------------
    // interpretation

    val r1 = run { evalms(List(mut_val,eval_val),App(App(App(eval_exp,Var(0)),Sym("nil-env")),Lit(4))) }

    check(r1)("Cst(24)")


    // generation + interpretation

    val c1 = reifyc { evalms(List(mut_val,eval_val),App(App(evalc_exp,Var(0)),Sym("nil-env"))) }

    check(c1)(mut_exp_anf.toString)

    val r2 = run { evalms(Nil,App(c1,Lit(4))) }

    check(r2)("Cst(24)")

    // we can show:
    // (evalms (evalc mut)) = mut
    // (evalms (evalc eval)) = eval
    // (evalms (evalc evalc)) = evalc



    // -----------------------------------------------
    // double interpretation!!

    // first try a plain value ... (evalms ((eval eval) 24)) = 24
    val r3 = run { evalms(List(mut_val,eval_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Lit(24)), Sym("nil-env2"))) }

    check(r3)("Cst(24)")


    // double eval mut ... (evalms (((eval eval) mut) 4)) = 24
    val r4 = run { evalms(List(mut_val,eval_val), App(App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2")), Lit(4))) }

    check(r4)("Cst(24)")


    // code generation through double interpretation !!!  (evalms ((eval evalc) mut)) = mut

    val c2 = reifyc { evalms(List(mut_val,evalc_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2"))) }

    check(c2)(mut_exp_anf.toString)

    val r5 = run { evalms(Nil,App(c2,Lit(4))) }

    check(r5)("Cst(24)")



    // now generate evaluator ... (evalms ((eval evalc) eval)) = eval

    val c3 = reifyc { evalms(List(eval_val,evalc_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0)), Sym("nil-env2"))) }

    // this is our evaluator!!!  
    // println("--- decompiled eval ---")
    // println(pretty(c3,Nil)) 
    //check(c3)(eval_exp_anf.toString)
    check(pretty(c3,Nil))(pretty(eval_exp_anf,Nil).toString) // compare prettyprinted b/c extra let

    // test that we can use the evaluator to run mut
    // NOTE: cannot put mut_val intro env!! 
    val r6 = run { val eval_val3 = evalms(Nil,c3); evalms(List(eval_val3,mut_val),App(App(App(Var(0),Var(1)), Sym("nil-env")), Lit(4))) }

    check(r6)("Cst(24)")



    // now generate generator ... (evalms ((eval evalc) evalc)) = evalc

    val c4 = reifyc { evalms(List(eval_val,evalc_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(1)), Sym("nil-env2"))) }

    // this is our generator!!!
    // println("--- decompiled evalc ---")
    // println(pretty(c4,Nil))
    //check(c4)(evalc_exp_anf.toString)
    check(pretty(c4,Nil))(pretty(evalc_exp_anf,Nil).toString) // compare prettyprinted b/c extra let

    val c5 = reifyc { val eval_valc4 = evalms(Nil,c4); evalms(List(eval_valc4,mut_val),App(App(Var(0),Var(1)), Sym("nil-env"))) }


    // this is mut, generated by decompiled evalc
    // println("--- mut generated by decompiled evalc ---")
    // println(pretty(c5,Nil)) 
    check(c5)(mut_exp_anf.toString)

    val r7 = run { evalms(Nil,App(c5,Lit(4))) }

    check(r7)("Cst(24)")

    // we have:
    // (evalms ((eval evalc) mut)) = mut
    // (evalms ((eval evalc) eval) = eval
    // (evalms ((eval evalc) evalc) = evalc


    // -----------------------------------------------
    // triple interpretation!!

    val eval_exp3 = trans(eval_val,List("arg","arg2","arg3")) // need three slots in env...

    // triple eval mut ... (evalms (((eval eval) evalc) mut)) = mut
    val c6 = reifyc { evalms(List(evalc_val,eval_val,mut_val), 
      App(App(App(App(App(App(App(App(eval_exp3,Var(1)),Sym("nil-env")), Var(1)), Sym("nil-env2")), Var(0)), Sym("nil-env3")), Var(2)), Sym("nil-env4"))) }

    check(c6)(mut_exp_anf.toString)
  }

  def testMutInEval() = {
    println("// ------- test mutation in eval --------")
    val counter_cell = new Cell(Cst(0))

    // -----------------------------------------------
    // interpretation
    val r1 = run { evalms(List(fac_val,eval_val,counter_cell),
      App(App(App(App(eval_vc_exp,Var(2)),Var(0)),Sym("nil-env")),Lit(4))) }
    check(r1)("Cst(24)")
    check(counter_cell.v)("Cst(13)")
    counter_cell.v = Cst(0)

    // generation + interpretation
    val c1 = reifyc { evalms(List(fac_val,eval_val,counter_cell),App(App(App(evalc_vc_exp,LiftRef(Var(2))),Var(0)),Sym("nil-env"))) }
    val expected = """
    |fun f0 x1 
    |  let x2 = RefExt(Base$Cell@XX)! in 
    |  let x3 = (x2 + 1) in 
    |  let x4 = (RefExt(Base$Cell@XX) := x3) in 
    |  if (x1) 
    |    let x5 = RefExt(Base$Cell@XX)! in 
    |    let x6 = (x5 + 1) in 
    |    let x7 = (RefExt(Base$Cell@XX) := x6) in 
    |    let x8 = RefExt(Base$Cell@XX)! in 
    |    let x9 = (x8 + 1) in 
    |    let x10 = (RefExt(Base$Cell@XX) := x9) in 
    |    let x11 = (x1 - 1) in 
    |    let x12 = (f0 x11) in (x1 * x12) 
    |  else 1""".stripMargin
    check(pretty(c1, Nil).replaceAll("@[0-9a-f]+","@XX"))(expected)
    check(counter_cell.v)("Cst(0)")
    val r2 = run { evalms(Nil,App(c1,Lit(4))) }
    check(r2)("Cst(24)")
    check(counter_cell.v)("Cst(13)")
  }


  def testEvalSyntax() = {
    println("// ------- test eval from lisp syntax --------")

    def run(src: String) = {
      val prog_src = s"""(let exec-quote (lambda _ src (exec (trans-quote src))) $src)"""
      val prog_val = parseExp(prog_src)
      val prog_exp = trans(prog_val,Nil)
      val res = reifyv(evalms(Nil,prog_exp))
      println(res)
      res
    }

    // plain exec
    run(s"""
    (let fac $fac_src 
    (fac 4))""")

    // quote + exec
    run(s"""
    (let fac_val   (quote $fac_src)
    (let fac       (exec-quote fac_val) ; evalms fac_val in current env, then evalms result in empty env
    (fac 4)))""")

    // exec (without quoting)
    run(s"""
    (let exec-quote/env (lambda _ src (exec/env 0 (trans-quote/env src)))
    (let fac_val   $fac_src
    (let fac       (exec/env 0 (trans-quote/env (quote (lambda _ n (fac_val n))))) ; evalms fac_val in current env, then evalms result in empty env
    (fac 4))))""")


    // quote + interpret
    run(s"""
    (let fac_val       (quote $fac_src)
    (let eval_poly     (lambda _ maybe-lift (lambda _ exp (($eval_poly_src exp) 'nil)))
    (let eval          (eval_poly (lambda _ e e))
    (let fac           (eval fac_val)
    (fac 4)))))""")

    // quote + compile
    run(s"""
    (let fac_val       (quote $fac_src)
    (let eval_poly     (lambda _ maybe-lift (lambda _ exp (($eval_poly_src exp) 'nil)))
    (let evalc         (eval_poly (lambda _ e (lift e)))
    (let fac           (exec (evalc fac_val)) ; evalc call must be in arg position (reify!)
    fac))))""")

    // quote + compile^2
    run(s"""
    (let fac_val       (quote $fac_src)
    (let eval_poly     (lambda _ maybe-lift (lambda _ exp (($eval_poly_src exp) 'nil)))
    (let evalc         (eval_poly (lambda _ e (lift (lift e))))
    (let fac           (evalc fac_val) ; evalc call must be in arg position (reify!)
    fac ))))""") // result is code



    // quote + compile with interpreted compiler
    run(s"""
    (let fac_val       (quote $fac_src)
    (let eval_poly_val (quote (lambda _ maybe-lift (lambda _ exp (($eval_poly_src exp) 'nil))))
    (let eval_poly     (exec-quote eval_poly_val)
    (let eval          (eval_poly (lambda _ e e))
    (let eval_poly2    (eval eval_poly_val)
    (let evalc2        (eval_poly2 (lambda _ e (lift e)))
    (let fac           (exec (evalc2 fac_val))
    (fac 4))))))))""")


    // test EM interpreted
    run(s"""
    (let eval_poly     (lambda _ maybe-lift (lambda _ exp (($eval_em_poly_src exp) 'nil)))
    (let eval          (eval_poly (lambda _ e e))
    (let fun           (eval (quote (lambda f x (EM (* 6 (env 'x))))))
    (fun 4))))""")

    // test EM compiled
    run(s"""
    (let eval_poly     (lambda _ maybe-lift (lambda _ exp (($eval_em_poly_src exp) 'nil)))
    (let evalc         (eval_poly (lambda _ e (lift e)))
    (let fun           (exec (evalc (quote (lambda f x (EM (* (lift 6) (env 'x)))))))
    ; fun compiles to (lambda f x (6 * x))
    (fun 4))))""")


    // EM + CPS interpreted
    run(s"""
    (let eval_poly     (lambda _ maybe-lift (lambda _ exp ((($eval_em_cps_poly_src exp) 'nil) (lambda k v v))))
    (let eval          (eval_poly (lambda _ e e))
    (let fun           (eval (quote (lambda f x (EM (k (+ (env 'x) 7))))))
    ((fun 3) (lambda k v v)))))""")
    

    // EM + CPS: implement shift as user-level function

    val shift = """
    (lambda _ f (EM (((env 'f) (maybe-lift (lambda _ v (maybe-lift (lambda _ k1 (k1 (k v))))))) (maybe-lift (lambda _ x x)))))
    """

    val example = s"""
    (let shift $shift
    (+ 3 (shift (lambda _ k (k (k (k 1)))))))
    """

    run(s"""
    (let eval_poly     (lambda _ maybe-lift (lambda _ exp ((($eval_em_cps_poly_src exp) 'nil) (lambda k v v))))
    (let eval          (eval_poly (lambda _ e e))
    (let res           (eval (quote $example))
    res)))""")

    // EM + CPS + shift + compiled
    run(s"""
    (let eval_poly     (lambda _ maybe-lift (lambda _ exp ((($eval_em_cps_poly_src exp) 'nil) (lambda k v v))))
    (let eval          (eval_poly (lambda _ e (lift e)))
    (let res           (eval (quote $example))
    res)))""")

    // amb using shift -- doesn't work!
    val amb = s"""
    (let foreach (lambda foreach xs (lambda _ k (if (isStr xs)
      (if (equs '. xs) 'done (k xs))
      (begin (k (car xs)) (foreach (cdr xs))))))
    (lambda _ xs (shift (lambda _ k ((foreach xs) k)))))
    """

    val example_amb = s"""
    (let shift $shift
    (let umb $amb
    (umb (cons (umb '()) '(1)))))
    """

    run(s"""
    (let eval_poly     (lambda _ maybe-lift (lambda _ exp ((($eval_em_cps_poly_src exp) 'nil) (lambda k v v))))
    (let eval          (eval_poly (lambda _ e e))
    (let res           (eval (quote $example_amb))
    res)))""")

    // note: lift eval_poly doesn't work
    run(s"""
    (let eval_poly     (lambda _ maybe-lift (lambda _ exp (($eval_em_poly_src exp) 'nil)))
    (let eval          (eval_poly (lambda _ e e))
    (let res           (eval (quote (((lambda _ x (EM env)) 1) 'x)))
    res)))""")
  }


  // EXPERIMENTAL
  def testUnstaging() = {
    println("// ------- test eval from lisp syntax --------")

    def run(src: String) = {
      val prog_src = s"""(let exec-quote (lambda _ src (exec (trans-quote src))) $src)"""
      val prog_val = parseExp(prog_src)
      val prog_exp = trans(prog_val,Nil)
      val res = reifyv(evalms(Nil,prog_exp))
      println(res)
      res
    }

    println("----- test unstaging (LMS mock-up) -----")

    // test case: call compilation again from compiled code

    case class Rep[T](s: Exp)

    def unit(x:Int): Rep[Int] = Rep(Lit(x))

    implicit class IntOps(x: Rep[Int]) {
      def *(y: Rep[Int]): Rep[Int] = Rep(reflect(Times(x.s,y.s)))
    }
    implicit class FunOps[A,B](x: Rep[A=>B]) {
      def call(y: Rep[A]): Rep[B] = Rep(reflect(App(x.s,y.s)))
    }


    val cell = new Cell(null)

    def compile[A,B](f: Rep[A] => Rep[B]): A => B = {
      val res = reify(f(Rep[A](fresh)).s)
      val code = Rep[A=>B](Lam(res))
      println(">>> compiled >>> ")
      println("  " + code.s)
      (x => ???)
    }

    def staticData[A](s:String, x: A): Rep[A] = Rep(Special(benv => Str(s)))

    def unstage[T,U](x: Rep[T])(f:T => Rep[U]): Rep[U] = {
      val ff: Rep[T => Rep[Int] => Rep[U]] = staticData("handler",x => ignore => f(x))
      val gg: Rep[Rep[Int] => Rep[U]] = ff.call(x)
      val cc: Rep[(Rep[Int] => Rep[U]) => (Int=>U)] = staticData("compile",compile[Int,U] _)
      val hh: Rep[Int => U] = cc.call(gg)
      hh.call(unit(-1))
    }

    compile { x: Rep[Int] =>
      unit(2) * x * unit(3)
    }

    compile { x: Rep[Int] =>
      unit(2) * unstage(x) { x2 =>  unit(x2 * 3) }
    }

    // problem case: recompiled code refers to stuff in env
    compile { x: Rep[Int] =>
      unit(2) * unstage(x) { x2 =>  unit(x2) * x } 
      // x is a variable that refers to code at generation time of original code
    }


    println("----- test unstaging / runtime re-compilation -----")
    traceExec = true

    // test 1
    run(s"""
    (let compile     (lambda _ x (exec (lift x)))
    (let fun         (compile (lambda f x (* (lift 2) x)))
    (fun 3)))""")
/*
    >>> compile: 
    fun f0 x1 (2 * x1)
    Cst(6)
*/


    // test 2
    run(s"""
    (let compile     (lambda _ x (exec (lift x)))
    (let unstage     (lambda _ x (lambda _ f 
      (let ff (lift-ref (lambda _ x2 (compile (lambda _ _ (f x2)))))
      (let hh (ff x)
      (hh (lift 'dummy))))))
    (let fun         (compile (lambda f x-dynamic
      (* (lift 2) ((unstage x-dynamic) (lambda _ x-static (lift (* x-static 3)))))))
    (* (fun 2) (fun 3)))))""")
/*
    >>> compile: 
    fun f0 x1 
      let x2 = (Special(<function1>) x1) in 
      let x3 = (x2 "dummy") in (2 * x3)
    >>> compile: 
    fun f0 x1 6
    >>> compile: 
    fun f0 x1 9
    Cst(216)
*/

    println("---XX---")

    // test 3
    run(s"""
    (let compile     (lambda _ x (exec (lift x)))
    (let compile2    (lambda _ x ((lift-ref compile) (lift x)))
    (let fun         (compile (lambda _ xd
      (* (lift 2) ((compile2 (lambda _ _ (lift (* xd (lift 3))))) (lift 'dummy)))))
    (fun 2))))""")




/*
    >>> compile: 
    fun f0 x1 
      let x2 = (Special(<function1>) x1) in 
      let x3 = (x2 "dummy") in (2 * x3)
    >>> compile: 
    fun f0 x1 6
    >>> compile: 
    fun f0 x1 9
    Cst(216)
*/


    // test 3 --- this fails with an exception (cannot refer to data in outer env)
    run(s"""
    (let compile     (lambda _ x (exec (lift x)))
    (let static      (lambda _ x (lift-ref x))
    (lift static )))""")
/*
    (let fun         (compile (lambda _ x
      ;((lift-ref compile) (lift (lambda _ y (+ (lift x) y))))))
      ((lift compile) (lift 7))))
    (fun 2))))""")
*/

  val feval_poly_src = """
  (lambda eval exp (lambda _ env
    (if (isNum               exp)       (maybe-lift exp)
    (if (isStr               exp)       (env exp)
    (if (isStr          (car exp))      
      (if (equs '+      (car exp))      (+  ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      (if (equs '-      (car exp))      (-  ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      (if (equs '*      (car exp))      (*  ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      (if (equs 'equs   (car exp))      (equs ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      (if (equs 'if     (car exp))      (if ((eval (cadr exp)) env) ((eval (caddr exp)) env) ((eval (cadddr exp)) env))
      (if (equs 'lambda (car exp))      (maybe-lift (lambda f x ((eval (cadddr exp)) (lambda _ y (if (equs y (cadr exp)) f (if (equs y (caddr exp)) x (env y)))))))
      (if (equs 'let    (car exp))      (let x ((eval (caddr exp)) env) ((eval (cadddr exp)) (lambda _ y (if (equs y (cadr exp)) x (env y)))))
      (if (equs 'lift       (car exp))      (lift       ((eval (cadr exp)) env))
      (if (equs 'lift-ref   (car exp))      (lift-ref   ((eval (cadr exp)) env))
      (if (equs 'nolift     (car exp))      (nolift     ((eval (cadr exp)) env))
      (if (equs 'nolift-ref (car exp))      (nolift-ref ((eval (cadr exp)) env))
      (if (equs 'isNum  (car exp))      (isNum ((eval (cadr exp)) env))
      (if (equs 'isStr  (car exp))      (isStr ((eval (cadr exp)) env))
      (if (equs 'cons   (car exp))      (maybe-lift (cons ((eval (cadr exp)) env) ((eval (caddr exp)) env)))
      (if (equs 'car    (car exp))      (car ((eval (cadr exp)) env))
      (if (equs 'cdr    (car exp))      (cdr ((eval (cadr exp)) env))
      (if (equs 'quote  (car exp))      (maybe-lift (cadr exp))
      (if (equs 'EM     (car exp))      'em-not-supported

      unstage x handler ===>  evalc

      (if (equs 'refNew (car exp))      (maybe-lift (refNew ((eval (cadr exp)) env)))
      (if (equs 'refRead (car exp))     (refRead ((eval (cadr exp)) env))
      (if (equs 'refWrite (car exp))    (refWrite ((eval (cadr exp)) env) ((eval (caddr exp)) env))
      ((env (car exp)) ((eval (cadr exp)) env)))))))))))))))))))))))
    (((eval (car exp)) env) ((eval (cadr exp)) env))
    )))))""".
    replace("(cadr exp)","(car (cdr exp))").
    replace("(caddr exp)","(car (cdr (cdr exp)))").
    replace("(cadddr exp)","(car (cdr (cdr (cdr exp))))")












    traceExec = false

  }

  def benchFac() = {
    import Bench._
    println("fac #,evaluated,compiled,traced evaluated,traced compiled")
    val counter_cell = new Cell(Cst(0))
    val fac_compiled = reifyc { evalms(List(fac_val,eval_val),App(App(evalc_exp,Var(0)),Sym("nil-env"))) }
    val fac_traced_compiled = reifyc { evalms(List(fac_val,eval_val,counter_cell),App(App(App(evalc_vc_exp,LiftRef(Var(2))),Var(0)),Sym("nil-env"))) }

    for (i <- 0 until 10) {
      val t1 = bench(run { evalms(List(fac_val,eval_val),App(App(App(eval_exp,Var(0)),Sym("nil-env")),Lit(i))) })
      val t2 = bench(run { evalms(Nil,App(fac_compiled,Lit(i))) })
      val t3 = bench(run { evalms(List(fac_val,eval_val,counter_cell),
        App(App(App(App(eval_vc_exp,Var(2)),Var(0)),Sym("nil-env")),Lit(i))) })
      val t4 = bench(run { evalms(Nil,App(fac_traced_compiled,Lit(i))) })
      println(s"$i,$t1,$t2,$t3,$t4")
    }
  }
}
