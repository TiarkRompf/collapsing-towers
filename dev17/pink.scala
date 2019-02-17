import Base._
import Lisp._

trait PinkBase {
  def commonReplace(s: String) = s.
    replace("num?", "isNum").
    replace("sym?", "isStr").
    replace("pair?", "isPair").
    replace("code?", "isCode").
    replace("eq?", "equs").
    replace("(cadr exp)","(car (cdr exp))").
    replace("(caddr exp)","(car (cdr (cdr exp)))").
    replace("(cadddr exp)","(car (cdr (cdr (cdr exp))))")

  val ev_src: String
  lazy val ev_val = parseExp(ev_src)
  lazy val ev_exp1 = trans(ev_val, List("arg1"))

  val evc_src: String
  lazy val evc_val = parseExp(evc_src)
  lazy val evc_exp1 = trans(evc_val, List("arg1"))

  def test() = {
    // interpretation of fac
    val r1 = run { evalms(List(fac_val), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lit(4))) }
    check(r1)("Cst(24)")

    // compilation of fac
    val c2 = reifyc { evalms(List(fac_val),App(App(evc_exp1,Var(0)),Sym("nil-env"))) }
    check(c2)(fac_exp_anf.toString)
    val r2 = run { evalms(Nil,App(c2,Lit(4))) }
    check(r2)("Cst(24)")

    // self-compilation
    val c3 = reifyc { evalms(List(ev_val),App(App(evc_exp1,Var(0)),Sym("nil-env"))) }
    val r3 = run { val v3 = evalms(Nil, c3); evalms(List(fac_val, v3), App(App(App(Var(1), Var(0)), Sym("nil-env")), Lit(4))) }
    check(r3)("Cst(24)")
  }
}

object Pink extends PinkBase {
  val ev_poly_src = commonReplace("""
(lambda _ maybe-lift (lambda _ eval (lambda _ exp (lambda _ env
  (if (num?                exp)    (maybe-lift exp)
  (if (sym?                exp)    (env exp)
  (if (sym?           (car exp))   
    (if (eq?  '+      (car exp))   (+   ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (eq?  '-      (car exp))   (-   ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (eq?  '*      (car exp))   (*   ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (eq?  'eq?    (car exp))   (eq? ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (eq?  'if     (car exp))   (if  ((eval (cadr exp)) env) ((eval (caddr exp)) env) ((eval (cadddr exp)) env))
    (if (eq?  'lambda (car exp))   (maybe-lift (lambda f x ((eval (cadddr exp)) 
      (lambda _ y (if (eq? y (cadr exp)) f (if (eq? y (caddr exp)) x (env y)))))))
    (if (eq?  'let    (car exp))   (let x ((eval (caddr exp)) env) ((eval (cadddr exp))
      (lambda _ y (if (eq?  y (cadr exp)) x (env y)))))
    (if (eq?  'lift   (car exp))   (lift ((eval (cadr exp)) env))
    (if (eq?  'num?   (car exp))   (num? ((eval (cadr exp)) env))
    (if (eq?  'sym?   (car exp))   (sym? ((eval (cadr exp)) env))
    (if (eq?  'car    (car exp))   (car  ((eval (cadr exp)) env))
    (if (eq?  'cdr    (car exp))   (cdr  ((eval (cadr exp)) env))
    (if (eq?  'cons   (car exp))   (maybe-lift (cons ((eval (cadr exp)) env) ((eval (caddr exp)) env)))
    (if (eq?  'quote  (car exp))   (maybe-lift (cadr exp))
    (if (eq?  'pair?  (car exp))   (pair? ((eval (cadr exp)) env))
    (if (eq?  'code?  (car exp))   (code? ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (equs 'refNew (car exp))      (maybe-lift (refNew ((eval (cadr exp)) env)))
    (if (equs 'refRead (car exp))     (refRead ((eval (cadr exp)) env))
    (if (equs 'refWrite (car exp))    (refWrite ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    ((env (car exp)) ((eval (cadr exp)) env)))))))))))))))))))))
  (((eval (car exp)) env) ((eval (cadr exp)) env)))))))))
""")

  val ev_src = s"""(lambda eval e ((($ev_poly_src (lambda _ e e)) eval) e))"""
  val evc_src = s"""(lambda eval e ((($ev_poly_src (lambda _ e (lift e))) eval) e))"""
}

object Pink_CPS extends PinkBase {
  val ev_poly_src = commonReplace("""
(lambda _ maybe-lift (lambda _ eval (lambda _ exp (lambda _ env (lambda _ k
  (if (num?                exp)    (k (maybe-lift exp))
  (if (sym?                exp)    (k (env exp))
  (if (sym?           (car exp))   
    (if (eq?  '+      (car exp))   (((eval (cadr exp)) env) (lambda _ v1 (((eval (caddr exp)) env) (lambda _ v2 (k (+ v1 v2))))))
    (if (eq?  '-      (car exp))   (((eval (cadr exp)) env) (lambda _ v1 (((eval (caddr exp)) env) (lambda _ v2 (k (- v1 v2))))))
    (if (eq?  '*      (car exp))   (((eval (cadr exp)) env) (lambda _ v1 (((eval (caddr exp)) env) (lambda _ v2 (k (* v1 v2))))))
    (if (eq?  'eq?    (car exp))   (((eval (cadr exp)) env) (lambda _ v1 (((eval (caddr exp)) env) (lambda _ v2 (k (eq? v1 v2))))))
    (if (eq?  'if     (car exp))   (((eval (cadr exp)) env) (lambda _ c (if c (((eval (caddr exp)) env) k) (((eval (cadddr exp)) env) k))))
    (if (eq?  'lambda (car exp))        (k (maybe-lift (lambda f x (maybe-lift ((eval (cadddr exp)) 
      (lambda _ y (if (eq? y (cadr exp)) f (if (eq? y (caddr exp)) x (env y)))))))))
    (if (eq?  'let    (car exp))   (((eval (caddr exp)) env) (maybe-lift (lambda _ v (let x v (((eval (cadddr exp)) (lambda _ y (if (eq?  y (cadr exp)) x (env y)))) k)))))
    (if (eq?  'lift   (car exp))   (((eval (cadr exp)) env) (lambda _ v (k (lift v))))
    (if (eq?  'num?   (car exp))   (((eval (cadr exp)) env) (lambda _ v (k (num? v))))
    (if (eq?  'sym?   (car exp))   (((eval (cadr exp)) env) (lambda _ v (k (sym? v))))
    (if (eq?  'car    (car exp))   (((eval (cadr exp)) env) (lambda _ v (k (car v))))
    (if (eq?  'cdr    (car exp))   (((eval (cadr exp)) env) (lambda _ v (k (cdr v))))
    (if (eq?  'cons   (car exp))   (((eval (cadr exp)) env) (lambda _ a (((eval (caddr exp)) env) (lambda _ d (k (maybe-lift (cons a d)))))))
    (if (eq?  'quote  (car exp))   (k (maybe-lift (cadr exp)))
    (((eval (cadr exp)) env) (lambda _ v2 (((env (car exp)) v2) (maybe-lift (lambda _ x (k x))))))))))))))))))))
  (((eval (car exp)) env) (lambda _ v1 (((eval (cadr exp)) env) (lambda _ v2 ((v1 v2) (maybe-lift (lambda _ x (k x))))))))))))))))
""")

  val ev_src = s"""(lambda eval e ((($ev_poly_src (lambda _ e e)) eval) e))"""
  val evc_src = s"""(lambda eval e ((($ev_poly_src (lambda _ e (lift e))) eval) e))"""

  override def test() = {
    // interpretation of fac
    val r1 = run { evalms(List(fac_val), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lam(App(App(Var(2),Lit(4)),Lam(Var(4)))))) }
    check(r1)("Cst(24)")

    // compilation of fac
    val c2 = reifyc { evalms(List(fac_val),App(App(App(evc_exp1,Var(0)),Sym("nil-env")),Lam(Var(2)))) }
    val r2 = run { evalms(Nil, App(App(c2, Lit(4)),Lam(Var(1)))) }
    check(r2)("Cst(24)")

    // self-compilation
    // note that we are using the regular compiler first, not the CPS one...
    val c3 = reifyc { evalms(List(ev_val),App(App(Pink.evc_exp1,Var(0)),Sym("nil-env"))) }
    val r3 = run { val v = evalms(Nil, c3); evalms(List(fac_val, v), App(App(App(Var(1), Var(0)), Sym("nil-env")), Lam(App(App(Var(3),Lit(4)),Lam(Var(5)))))) }
    check(r3)("Cst(24)")
    // ... now the CPS one
    val c4 = reifyc { evalms(List(ev_val), App(App(App(evc_exp1,Var(0)), Sym("nil-env")), Lam(Var(2)))) }
    // ... but the evaluator got CPSed too!
    // ... and it's super confusing!
    val fac_app_src = s"($fac_src 4)"
    val r4 = run { val v = evalms(Nil, c4); evalms(List(parseExp(fac_app_src), v), App(App(App(App(Var(1), Var(0)), Lam(App(App(Var(3), Sym("nil-env")),Lam(Var(5))))),
      Lam(Lam(Var(3)))), // somehow we have to thunk the result
      Lit(0))) // force the thunk
    }
    check(r4)("Cst(24)")
    val r5 = run { val v = evalms(Nil, c4); evalms(List(fac_val, v), App(App(App(App(App(App(Var(1), Var(0)), Lam(App(App(Var(3), Sym("nil-env")),Lam(Var(5))))),
      Lam(App(Var(3),Lit(4)))),
      Lam(Var(3))),
      Lam(Lam(Var(3)))),
      Lit(0)))
    }
    check(r5)("Cst(24)")

    val nested_src = "(lambda f n (if (if n 0 1) 2 3))"
    val nested_val = parseExp(nested_src)
    val r6 = run { evalms(List(nested_val), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lam(App(App(Var(2),Lit(0)),Lam(Var(4)))))) }
    check(r6)("Cst(2)")

    val c6 = reifyc { evalms(List(nested_val),App(App(App(evc_exp1,Var(0)),Sym("nil-env")),Lam(Var(2)))) }
    val r7 = run { evalms(Nil, App(App(c6, Lit(0)), Lam(Var(1)))) }
    check(r7)("Cst(2)")

    println("nested:"+pretty(c6,Nil))

  }
}

object Pink_clambda extends PinkBase {
  val ev_poly_src = commonReplace("""
(lambda tie eval (lambda _ l (lambda _ exp (lambda _ env
  (if (num?                exp)    ((car l) exp)
  (if (sym?                exp)    (env exp)
  (if (sym?           (car exp))   
    (if (eq?  '+      (car exp))   (+   (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  '-      (car exp))   (-   (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  '*      (car exp))   (*   (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  'eq?    (car exp))   (eq? (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  'if     (car exp))   (if  (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env) (((eval l) (cadddr exp)) env))
    (if (if (eq? 'lambda (car exp)) 1 (if (eq? 'clambda (car exp)) (cdr l) 0)) ((car l) (lambda f x (((eval l) (cadddr exp))
      (lambda _ y (if (eq? y (cadr exp)) f (if (eq? y (caddr exp)) x (env y)))))))
    (if (eq? 'clambda (car exp))       (exec 0 (((eval (cons (lambda _ e (lift e)) 1)) (cons 'lambda (cdr exp)))  (lambda _ y (lift-ref (env y)))))
    (if (eq?  'let    (car exp))   (let x (((eval l) (caddr exp)) env) (((eval l) (cadddr exp))
      (lambda _ y (if (eq?  y (cadr exp)) x (env y)))))
    (if (eq?  'lift   (car exp))   (lift (((eval l) (cadr exp)) env))
    (if (eq? 'lift-ref (car exp))  (lift-ref (((eval l) (cadr exp)) env))
    (if (eq?  'num?   (car exp))   (num? (((eval l) (cadr exp)) env))
    (if (eq?  'sym?   (car exp))   (sym? (((eval l) (cadr exp)) env))
    (if (eq?  'pair?  (car exp))   (pair? (((eval l) (cadr exp)) env))
    (if (eq?  'car    (car exp))   (car  (((eval l) (cadr exp)) env))
    (if (eq?  'cdr    (car exp))   (cdr  (((eval l) (cadr exp)) env))
    (if (eq?  'cons   (car exp))   ((car l) (cons (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env)))
    (if (eq?  'quote  (car exp))   ((car l) (cadr exp))
    (if (eq?  'exec   (car exp))   (exec (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  'scope (car exp))    (let ev (((eval (cons (lambda _ e e) (cdr l))) (cadr exp)) env) (((ev l) (caddr exp)) env))
    (if (eq?  'open  (car exp))    (let ev (((eval (cons (lambda _ e e) (cdr l))) (cadr exp)) env) (((((ev tie) eval) l) (caddr exp)) env))
    (if (eq?  'log    (car exp))   (log (((eval l) (cadr exp)) env))
    (if (eq?  'EM     (car exp))   (exec/env 0 (trans-quote/env (car (cdr exp))))
    (if (eq?  'exec/env (car exp)) (exec/env (((eval l) (cadr exp)) env) (((eval l) (caddr exp)) env))
    (if (eq?  'trans-quote/env (car exp)) (trans-quote/env (cadr exp))
    ((env (car exp)) (((eval l) (cadr exp)) env))))))))))))))))))))))))))
  ((((eval l) (car exp)) env) (((eval l) (cadr exp)) env)))))))))
""")

  val ev_tie_src = s"""(lambda eval l (lambda _ e ((($ev_poly_src eval) l) e)))"""
  val ev_src = s"""($ev_tie_src (cons (lambda _ e e) 0))"""
  val evc_src = s"""($ev_tie_src (cons (lambda _ e (lift e)) 1))"""
  val fc_src = fac_src.replace("lambda", "clambda")
  val fc_val = parseExp(fc_src)

  // translated to Pink from Scheme at https://github.com/jasonhemann/microKanren/blob/master/microKanren.scm
  val microKanren = commonReplace("""
(let = (lambda _ a (lambda _ b (if (- a b) 0 1)))
(let null? (lambda _ l (if (sym? l) (eq? l '.) 0))
(let assp (lambda assp p (lambda _ s (if (pair? s) (if (p (car (car s))) (car s) ((assp p) (cdr s))) s)))
(let var (lambda _ c (cons 'var c))
(let var? (lambda _ x (if (pair? x) (if (sym? (car x)) (eq? 'var (car x)) 0) 0))
(let var=? (lambda _ x1 (lambda _ x2 ((= (cdr x1)) (cdr x2))))
(let walk (lambda walk u (lambda _ s
  (let pr (if (var? u) ((assp (var=? u)) s) '.)
    (if (null? pr) u ((walk (cdr pr)) s)))))
(let ext-s (lambda _ x (lambda _ v (lambda _ s (cons (cons x v) s))))
(let mzero '.
(let unit (lambda _ s/c (cons s/c mzero))
(let unify (lambda unify u (lambda _ v (lambda _ s
  (let u ((walk u) s)
  (let v ((walk v) s)
  (if (if (var? u) (if (var? v) ((var=? u) v) 0) 0) s
  (if (var? u) (((ext-s u) v) s)
  (if (var? v) (((ext-s v) u) s)
  (if (if (pair? u) (pair? v) 0)
      (let s (((unify (car u)) (car v)) s)
         (if (pair? s) (((unify (cdr u)) (cdr v)) s) 0))
  (if (eq? u v) s '.))))))))))
(let == (lambda _ u (lambda _ v (lambda _ s/c
    (let s (((unify u) v) (car s/c))
      (if (pair? s) (unit (cons s (cdr s/c))) mzero)))))
(let call/fresh (lambda _ f (lambda _ s/c
    (let c (cdr s/c)
      ((f (var c)) (cons (car s/c) (+ c 1))))))
(let mplus (lambda mplus $1 (lambda _ $2
  (if (null? $1) $2
  (if (pair? $1) (cons (car $1) ((mplus (cdr $1)) $2))
   ;; (procedure? $1)
   (lambda _ _ ((mplus $2) ($1 0)))))))
(let bind (lambda bind $ (lambda _ g
  (if (null? $) mzero
  (if (pair? $) ((mplus (g (car $))) ((bind (cdr $)) g))
  ;; (procedure? $)
  (lambda _ _ ((bind ($ 0)) g))))))
(let disj (lambda _ g1 (lambda _ g2 (lambda _ s/c ((mplus (g1 s/c)) (g2 s/c)))))
(let conj (lambda _ g1 (lambda _ g2 (lambda _ s/c ((bind (g1 s/c)) g2))))
(let empty-state (cons '. 0)
program
))))))))))))))))))
""")

  def addParen(p: (Boolean, String)) = {
    val (need_paren, s) = p
    if (need_paren) "("+s.trim()+")" else s
  }
  def pp(r: Val): (Boolean,String) = r match {
    case Cst(n) => (false, n.toString)
    case Str(s) if s=="." => (true, "")
    case Tup(Str(s), Cst(n)) if s=="var" => (false, s"#(${n.toString})")
    case Tup(a, b) =>
      val s1 = addParen(pp(a))
      val (p2, s2) = pp(b)
      (true, s1+(if (p2) " " else " . ")+s2)
  }
  def show(r: Val): String = addParen(pp(r))

  def test_mk() = {
    val env = trans(parseExp("(lambda _ err (lambda _ y (err (log y))))"), List("arg1"))
    def atest(p: String, e: String) {
      val v = parseExp(microKanren.replace("program", p))
      val r = run { evalms(List(v), App(App(ev_exp1, Var(0)), App(env, Sym("nil-env")))) }
      check(show(r))(e)
    }
    atest("(let p ((call/fresh (lambda _ q ((== q) 5))) empty-state) (car p))", "(((#(0) . 5)) . 1)")
    atest("(let p ((call/fresh (lambda _ q ((== q) 5))) empty-state) (cdr p))", "()")
    val a_and_b = """
  ((conj
   (call/fresh (lambda _ a ((== a) 7))))
   (call/fresh
    (lambda _ b
      ((disj
       ((== b) 5))
       ((== b) 6)))))"""
    atest(s"(let p ($a_and_b empty-state) (car p))", "(((#(1) . 5) (#(0) . 7)) . 2)")
    atest(s"(let p ($a_and_b empty-state) (car (cdr p)))", "(((#(1) . 6) (#(0) . 7)) . 2)")
    atest(s"(let p ($a_and_b empty-state) (cdr (cdr p)))", "()")
  }

  def test_clambda() = {
    val r1 = run { evalms(List(fc_val), App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(4))) }
    check(r1)("Cst(24)")
    val c1 = (run { evalms(List(fc_val), App(App(ev_exp1, Var(0)),Sym("nil-env"))) }).asInstanceOf[Clo]
    check(c1.env)("List()")
    check(pretty(c1.e, List("r", "n")))("""
if (n) 
  let x2 = (n - 1) in 
  let x3 = (r x2) in (n * x3) 
else 1""") // all interpretation overhead is gone

    println("closure 2")
    val c2_val = parseExp("(lambda _ x (clambda _ y (* (+ x x) y)))")
    val r2 = run { evalms(List(c2_val), App(App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(1)),Lit(4))) }
    check(r2)("Cst(8)")

    println("closure 3")
    val c3_val = parseExp("(clambda _ x (lambda _ y (* (+ x x) y)))")
    val r3 = run { evalms(List(c3_val), App(App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(1)),Lit(4))) }
    check(r3)("Cst(8)")

    println("closure 4")
    val c4_val = parseExp("(clambda _ x (clambda _ y (* (+ x x) y)))")
    val r4 = run { evalms(List(c4_val), App(App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(1)),Lit(4))) }
    check(r4)("Cst(8)")

    val c5_val = parseExp("(let inc (lambda _ x (+ x 1)) (clambda _ y (inc y)))")
    val r5 = run { evalms(List(c5_val), App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(4))) }
    check(r5)("Cst(5)")

    val c6_val = parseExp("(lambda _ x (clambda _ y (lambda _ l (* (l (+ x x)) (l y)))))")
    val r6 = run { evalms(List(c6_val), App(App(App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(1)),Lit(4)),Lam(Var(2)))) }
    val c6 = (run { evalms(List(c6_val), App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(1))) }).asInstanceOf[Clo]
    println(pretty(c6.e, List("r", "y")))
    check(r6)("Cst(8)")
    val c7 = reifyc { evalms(List(c6_val), App(App(App(App(App(ev_exp1, Var(0)),Sym("nil-env")),Lit(1)),Lit(4)),Lam(Lift(Var(2))))) }
    println(c7)
  }

  def test_log() {
    run { evalms(List(parseExp("(log 1)")), App(App(ev_exp1, Var(0)),Sym("nil-env"))) }
  }

  def test_em() {
    println("begin test_EM")
    val ev_log_src = commonReplace(ev_tie_src.replace("(env exp)", "(if (eq? 'n exp) (log (env exp)) (env exp))"))
    val v1 = run { evalms(List(parseExp(s"(EM ((($ev_log_src l) '($fac_src 4)) env))")), App(App(ev_exp1, Var(0)), Sym("nil-env"))) }
    check(v1)("Cst(24)")
    val v2 = run { evalms(List(parseExp(s"(EM ((($ev_log_src l) '(${fac_src.replace("lambda", "clambda")} 4)) env))")), App(App(ev_exp1, Var(0)), Sym("nil-env"))) }
    check(v2)("Cst(24)")
    val v3 = run { evalms(List(parseExp(commonReplace(s"""(EM ((((lambda ev l (lambda _ exp (lambda _ env
    (if (if (sym? exp) (eq? 'n exp) 0) (log (((eval l) exp) env))
    ((((tie ev) l) exp) env))))) l) '($fac_src 4)) env))"""))), App(App(ev_exp1, Var(0)), Sym("nil-env"))) }
    check(v3)("Cst(24)")
    val v4 = run { evalms(List(parseExp(commonReplace(s"""(EM ((((lambda ev l (lambda _ exp (lambda _ env
    (if (if (sym? exp) (eq? 'n exp) 0) (log (((eval l) exp) env))
    ((((tie ev) l) exp) env))))) l) '(${fac_src.replace("lambda", "clambda")} 4)) env))"""))), App(App(ev_exp1, Var(0)), Sym("nil-env"))) }
    check(v4)("Cst(24)")
    println("end test_EM")
  }

  def test_scope() {
    println("begin test_scope")
    val ev_log_src = commonReplace(ev_tie_src.replace("(env exp)", "(if (eq? 'n exp) (log (env exp)) (env exp))"))
    println("uncompiled ev")
    testMeta(s"scope $ev_log_src")
    println("compiled ev")
    testMeta(s"scope ((clambda _ _ $ev_log_src) 0)")
    println("end test_scope")
  }

  def test_open() {
    println("test_open")
    val s = commonReplace("""open (lambda _ tie (lambda _ eval (lambda ev l (lambda _ exp (lambda _ env

(if (if (sym? exp) (eq? 'n exp) 0) (log (((eval l) exp) env))
((((tie ev) l) exp) env))

)))))""")
    println("uncompiled ev")
    testMeta(s)
    println("compiled ev")
    testMeta(s.replace("open (lambda", "open (clambda"))
    println("end test_open")
  }

  def testMeta(s: String) {
    run { evalms(List(parseExp(s"($s ((lambda _ x x) 2))")), App(App(ev_exp1, Var(0)),Sym("nil-env"))) }
    run { evalms(List(parseExp(s"($s ((lambda _ n n) 3))")), App(App(ev_exp1, Var(0)),Sym("nil-env"))) }
    run { evalms(List(parseExp(s"($s ((lambda _ n (+ n n)) 3))")), App(App(ev_exp1, Var(0)),Sym("nil-env"))) }
    run { evalms(List(parseExp(s"($s ($fac_src 4))")), App(App(ev_exp1, Var(0)),Sym("nil-env"))) }

    val c_inc = run { evalms(List(parseExp(s"($s (clambda _ n (+ n 1)))")), App(App(ev_exp1, Var(0)),Sym("nil-env"))) }.asInstanceOf[Clo]
    check(c_inc.env)("List()")
    println("compiled inc:")
    println(pretty(c_inc.e, List("r", "n")))

    val c_fac = run { evalms(List(parseExp(s"($s $fc_src)")), App(App(ev_exp1, Var(0)),Sym("nil-env"))) }.asInstanceOf[Clo]
    check(c_fac.env)("List()")
    println("compiled fac:")
    println(pretty(c_fac.e, List("r", "n")))

    val c_1 = run { evalms(List(parseExp(s"(clambda _ _ ($s 1))")), App(App(ev_exp1, Var(0)),Sym("nil-env"))) }.asInstanceOf[Clo]
    check(c_1.env)("List()")
    println("compiled constant fun:")
    println(pretty(c_1.e, List("r", "n")))

    val c_id = run { evalms(List(parseExp(s"(clambda _ n ($s n))")), App(App(ev_exp1, Var(0)),Sym("nil-env"))) }.asInstanceOf[Clo]
    check(c_id.env)("List()")
    println("compiled id fun, with tracing:")
    println(pretty(c_id.e, List("r", "n")))
  }

  override def test() = {
    super.test()
    println("-- BEGIN pink clambda")
    val oldTrace = traceExec
    try {
      traceExec = true
      test_clambda()
      test_log()
      test_em()
      test_scope()
      test_open()
      test_mk()
      println("-- END pink clambda")
    } finally { traceExec = oldTrace }
  }
}

object Pink_macro extends PinkBase {
  val ev_poly_src = commonReplace("""
(let macro? (lambda _ v1 (if (code? 0 v1) 0 (if (pair? v1) (if (sym? (car v1)) (eq? 'macro (car v1)) 0) 0)))

(lambda _ eval (lambda _ l (lambda _ exp (lambda _ env (lambda _ k

(let app (lambda _ _

   ((((eval l) (car exp)) env) (lambda _ v1
     (if (macro? v1) (((cdr v1) (cdr exp)) (lambda _ v ((((eval l) v) env) (l (lambda _ x (k x))))))
     ((((eval l) (cadr exp)) env) (lambda _ v2 ((v1 v2) (l (lambda _ x (k x)))))))))

)

  (if (num?                exp)    (k (l exp))
  (if (sym?                exp)    (k (env exp))
  (if (sym?           (car exp))   
    (if (eq?  '+      (car exp))   ((((eval l) (cadr exp)) env) (lambda _ v1 ((((eval l) (caddr exp)) env) (lambda _ v2 (k (+ v1 v2))))))
    (if (eq?  '-      (car exp))   ((((eval l) (cadr exp)) env) (lambda _ v1 ((((eval l) (caddr exp)) env) (lambda _ v2 (k (- v1 v2))))))
    (if (eq?  '*      (car exp))   ((((eval l) (cadr exp)) env) (lambda _ v1 ((((eval l) (caddr exp)) env) (lambda _ v2 (k (* v1 v2))))))
    (if (eq?  'eq?    (car exp))   ((((eval l) (cadr exp)) env) (lambda _ v1 ((((eval l) (caddr exp)) env) (lambda _ v2 (k (eq? v1 v2))))))
    (if (eq?  'if     (car exp))   ((((eval l) (cadr exp)) env) (lambda _ c (if c ((((eval l) (caddr exp)) env) k) ((((eval l) (cadddr exp)) env) k))))
    (if (eq?  'lambda (car exp))        (k (l (lambda f x (l (((eval l) (cadddr exp)) 
      (lambda _ y (if (eq? y (cadr exp)) f (if (eq? y (caddr exp)) x (env y)))))))))
    (if (eq?  'macro (car exp))    (k (cons 'macro (lambda f x (((eval (lambda _ e e)) (cadddr exp)) 
      (lambda _ y (if (eq? y (cadr exp)) (cons 'macro f) (if (eq? y (caddr exp)) x (env y))))))))
    (if (eq?  'let    (car exp))   ((((eval l) (caddr exp)) env) (l (lambda _ v (let x v ((((eval l) (cadddr exp)) (lambda _ y (if (eq?  y (cadr exp)) x (env y)))) k)))))
    (if (eq?  'lift   (car exp))   ((((eval l) (cadr exp)) env) (lambda _ v (k (lift v))))
    (if (eq?  'num?   (car exp))   ((((eval l) (cadr exp)) env) (lambda _ v (k (num? v))))
    (if (eq?  'sym?   (car exp))   ((((eval l) (cadr exp)) env) (lambda _ v (k (sym? v))))
    (if (eq?  'pair?   (car exp))   ((((eval l) (cadr exp)) env) (lambda _ v (k (pair? v))))
    (if (eq?  'car    (car exp))   ((((eval l) (cadr exp)) env) (lambda _ v (k (car v))))
    (if (eq?  'cdr    (car exp))   ((((eval l) (cadr exp)) env) (lambda _ v (k (cdr v))))
    (if (eq?  'cons   (car exp))   ((((eval l) (cadr exp)) env) (lambda _ a ((((eval l) (caddr exp)) env) (lambda _ d (k (l (cons a d)))))))
    (if (eq?  'quote  (car exp))   (k (l (cadr exp)))
    (if (eq? 'call/cc (car exp))   (((((eval l) (cadr exp)) env) (lambda _ p (p (l (lambda _ v (l (lambda _ k1 (k v))))))))  (l (lambda _ v (k v))))
    (if (equs 'refNew (car exp))      ((((eval l) (cadr exp)) env) (lambda _ v (k (l (refNew v)))))
    (if (equs 'refRead (car exp))     ((((eval l) (cadr exp)) env) (lambda _ v (k (refRead v))))
    (if (equs 'refWrite (car exp))    ((((eval l) (cadr exp)) env) (lambda _ v1 ((((eval l) (caddr exp)) env) (lambda _ v2 (k (refWrite v1 v2))))))

(app 0)

))))))))))))))))))))

(app 0)

))))))))))
""")

  val ev_tie_src = s"""(lambda eval l (lambda _ e ((($ev_poly_src eval) l) e)))"""
  val ev_src = s"""($ev_tie_src (lambda _ e e))"""
  val evc_src = s"""($ev_tie_src (lambda _ e (lift e)))"""

  override def test() = {
    // baby tests for when nothing was working..
    val v0 = parseExp("(+ 1 2)")
    val r0 = run { evalms(List(v0), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lam(Var(2)))) }
    check(r0)("Cst(3)")

    val va = parseExp("(lambda _ x (+ x x))")
    val ra = run { evalms(List(va), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lam(App(App(Var(2), Lit(2)), Lam(Var(4)))))) }
    check(ra)("Cst(4)")

    val vb = parseExp("(lambda f n (if n (+ 1 (f (- n 1))) 0))")
    val rb = run { evalms(List(vb), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lam(App(App(Var(2), Lit(2)), Lam(Var(4)))))) }
    check(rb)("Cst(2)")

    // interpretation of fac
    val r1 = run { evalms(List(fac_val), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lam(App(App(Var(2),Lit(4)),Lam(Var(4)))))) }
    check(r1)("Cst(24)")

    // compilation of fac
    val c2 = reifyc { evalms(List(fac_val),App(App(App(evc_exp1,Var(0)),Sym("nil-env")),Lam(Var(2)))) }
    val r2 = run { evalms(Nil, App(App(c2, Lit(4)),Lam(Var(1)))) }
    check(r2)("Cst(24)")

    // macro tests
    val v3 = parseExp("((macro _ e (car e)) 1)")
    val r3 = run { evalms(List(v3), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lam(Var(2)))) }
    check(r3)("Cst(1)")

    val v4 = parseExp("((macro _ e (car e)) (+ 1 0))")
    val r4 = run { evalms(List(v4), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lam(Var(2)))) }
    check(r4)("Cst(1)")


    // begin as a macro
    def begin_src(body: String) = commonReplace(s"""
      (let begin-list (lambda rec xs (if (sym? (cdr xs)) (car xs)
         (cons (cons 'lambda (cons '_ (cons '_ (cons (rec (cdr xs)) '.))))
         (cons (car xs) '.))))
      (let begin (macro _ xs (begin-list xs))
      $body
      ))""")
    val v5 = parseExp(begin_src("(begin 1 2 3)"))
    val r5 = run { evalms(List(v5), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lam(Var(2)))) }
    check(r5)("Cst(3)")

    // amb as a macro
    def amb_src(body: String) = commonReplace(s"""
(let amb-fail (refNew (lambda _ () 'error))
    (let amb (macro _ xs
(cons 'let (cons 'prev-amb-fail (cons '(refRead amb-fail) (cons

(cons 'call/cc (cons (cons 'lambda (cons '_ (cons 'sk
(cons (cons 'begin
(((lambda map f (lambda _ xs (if (if (isStr xs) (equs '. xs) 0)
(cons '(prev-amb-fail 1) '.)
(cons (f (car xs)) ((map f) (cdr xs))))))
 (lambda _ alt (cons 'call/cc (cons (cons 'lambda (cons '_ (cons 'fk (cons (cons 'begin
   (cons (cons 'refWrite (cons 'amb-fail
(cons (cons 'lambda (cons '_ (cons '_ (cons (cons 'begin (cons '(refWrite amb-fail prev-amb-fail) (cons (cons 'fk (cons 0 '.)) '.))) '.)))) '.)))
   (cons (cons 'sk (cons alt '.)) '.))) '.)))) '.)))) xs))'.)
))) '.))


'.)))))
$body
))""")
    def all_amb(body: String) = begin_src(amb_src(body))
    def test_amb(body: String, expected: String) = {
      val v = parseExp(all_amb(body))
      val r = run { evalms(List(v), App(App(App(ev_exp1, Var(0)), Sym("nil-env")), Lam(Var(2)))) }
      check(r)(expected)
    }
    test_amb("(amb 1)", "Cst(1)")
    test_amb("(amb (amb) (amb 1))", "Cst(1)")

    // self-compilation
    val c = reifyc { evalms(List(ev_val),App(App(Pink.evc_exp1,Var(0)),Sym("nil-env"))) }
    val r6 = run { val v = evalms(Nil, c); evalms(List(fac_val, v), App(App(App(Var(1), Var(0)), Sym("nil-env")), Lam(App(App(Var(3),Lit(4)),Lam(Var(5)))))) }
    check(r6)("Cst(24)")

    val r7 = run { val v = evalms(Nil, c); evalms(List(v3, v), App(App(App(Var(1), Var(0)), Sym("nil-env")), Lam(Var(3)))) }
    check(r7)("Cst(1)")

    val r8 = run { val v = evalms(Nil, c); evalms(List(v5, v), App(App(App(Var(1), Var(0)), Sym("nil-env")), Lam(Var(3)))) }
    check(r8)("Cst(3)")

    val r9 = run { val v = evalms(Nil, c); evalms(List(parseExp(all_amb("(amb 1)")), v), App(App(App(Var(1), Var(0)), Sym("nil-env")), Lam(Var(3)))) }
    check(r9)("Cst(1)")
  }
}
