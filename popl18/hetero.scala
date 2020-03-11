import Base._
import Lisp._
import PinkBase._
import Pink._

object Hetero {
  val ev_hetero_poly_src = """
(lambda _ my-+ (lambda _ my-- (lambda _ my-* (lambda _ my-num? (lambda _ my-num (lambda _ maybe-lift (lambda tie eval (lambda _ exp (lambda _ env
  (if (num?                exp)    (maybe-lift (my-num exp))
  (if (sym?                exp)    (env exp)
  (if (sym?           (car exp))
    (if (eq?  '+      (car exp))   ((my-+   ((eval (cadr exp)) env)) ((eval (caddr exp)) env))
    (if (eq?  '-      (car exp))   ((my--   ((eval (cadr exp)) env)) ((eval (caddr exp)) env))
    (if (eq?  '*      (car exp))   ((my-*   ((eval (cadr exp)) env)) ((eval (caddr exp)) env))
    (if (eq?  'eq?    (car exp))   (eq? ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (eq?  'if     (car exp))   (if  ((eval (cadr exp)) env) ((eval (caddr exp)) env) ((eval (cadddr exp)) env))
    (if (eq?  'lambda (car exp))   (maybe-lift (lambda f x ((eval (cadddr exp)) 
      (lambda _ y (if (eq? y (cadr exp)) f (if (eq? y (caddr exp)) x (env y)))))))
    (if (eq?  'let    (car exp))   (let x ((eval (caddr exp)) env) ((eval (cadddr exp))
      (lambda _ y (if (eq?  y (cadr exp)) x (env y)))))
    (if (eq?  'lift   (car exp))   (lift ((eval (cadr exp)) env))
    (if (eq?  'num?   (car exp))   (my-num? ((eval (cadr exp)) env))
    (if (eq?  'sym?   (car exp))   (sym? ((eval (cadr exp)) env))
    (if (eq?  'car    (car exp))   (car  ((eval (cadr exp)) env))
    (if (eq?  'cdr    (car exp))   (cdr  ((eval (cadr exp)) env))
    (if (eq?  'cadr   (car exp))   (cadr  ((eval (cadr exp)) env))
    (if (eq?  'caddr  (car exp))   (caddr  ((eval (cadr exp)) env))
    (if (eq?  'cadddr (car exp))   (cadddr  ((eval (cadr exp)) env))
    (if (eq?  'cons   (car exp))   (maybe-lift (cons ((eval (cadr exp)) env) ((eval (caddr exp)) env)))
    (if (eq?  'quote  (car exp))   (maybe-lift (cadr exp))
    (if (eq?  'pair?  (car exp))   (pair? ((eval (cadr exp)) env))
    (if (eq?  'run    (car exp))   (run ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    (if (eq?  'log    (car exp))   (log ((eval (cadr exp)) env) ((eval (caddr exp)) env))
    ((env (car exp)) ((eval (cadr exp)) env))))))))))))))))))))))
  (((eval (car exp)) env) ((eval (cadr exp)) env))))))))))))))
"""

  val eval_poly_src0 = s"((((($ev_hetero_poly_src (lambda _ x (lambda _ y (+ x y)))) (lambda _ x (lambda _ y (- x y)))) (lambda _ x (lambda _ y (* x y)))) (lambda _ x (num? x))) (lambda _ x x))"
  val eval_poly_src1 = s"((((($ev_hetero_poly_src (lambda _ x (lambda _ y (cons 'num (+ (cdr x) (cdr y)))))) (lambda _ x (lambda _ y (cons 'num (- (cdr x) (cdr y)))))) (lambda _ x (lambda _ y (cons 'num (* (cdr x) (cdr y)))))) (lambda _ x (if (pair? x) (eq? (car x) 'num) 0))) (lambda _ x (cons 'num x)))"

  val eval_src0 = ev_nil(ev_nolift(eval_poly_src0))
  val eval_src1 = ev_nil(ev_nolift(eval_poly_src1))
  val evalc_src0 = ev_nil(ev_lift(eval_poly_src0))
  val eval_poly2_src1 = s"((((($ev_hetero_poly_src (lambda _ x (lambda _ y (+ x y)))) (lambda _ x (lambda _ y (- x y)))) (lambda _ x (lambda _ y (* x y)))) (lambda _ x (if (pair? x) (eq? (car x) 'num) 0))) (lambda _ x (cons 'num x)))"
  def ev_liftmy(src: String) = s"(lambda eval e ((($src (lambda _ e (lift (if (pair? e) (if (eq? 'num (car e)) (cdr e) e) e)))) eval) e))"
  val evalc_src1 = ev_nil(ev_liftmy(eval_poly2_src1))

  def test() = {
    println("// ------- Hetero.test --------")

    println("Correctness and optimality...")
    // direct execution
    checkrun(s"""
    (let fac $fac_src 
    (fac 4))""",
    "Cst(24)")

    // interpretation
    checkrun(s"""
    (let eval          $eval_src0
    (let fac_src       (quote $fac_src)

    ((eval fac_src) 4)))""",
    "Cst(24)")

    checkrun(s"""
    (let eval          $eval_src1
    (let fac_src       (quote $fac_src)

    ((eval fac_src) (cons 'num 4))))""",
    "Tup(Str(num),Cst(24))")

    // double interpretation
    checkrun(s"""
    (let eval          $eval_src0
    (let fac_src       (quote $fac_src)
    (let eval_src      (quote $eval_src0)

    (((eval eval_src) fac_src) 4))))""",
    "Cst(24)")

    checkrun(s"""
    (let eval          $eval_src0
    (let fac_src       (quote $fac_src)
    (let eval_src      (quote $eval_src1)

    (((eval eval_src) fac_src) (cons 'num 4)))))""",
    "Tup(Str(num),Cst(24))")

    // triple interpretation
    checkrun(s"""
    (let eval          $eval_src0
    (let fac_src       (quote $fac_src)
    (let eval_src      (quote $eval_src0)

    ((((eval eval_src) eval_src) fac_src) 4))))""",
    "Cst(24)")

    checkrun(s"""
    (let eval          $eval_src0
    (let fac_src       (quote $fac_src)
    (let eval_src0      (quote $eval_src0)
    (let eval_src1      (quote $eval_src1)

    ((((eval eval_src0) eval_src1) fac_src) (cons 'num 4))))))""",
    "Tup(Str(num),Cst(24))")

    // compilation
    checkcode(s"""
    (let evalc         $evalc_src0
    (let fac_src       (quote $fac_src)

    (evalc fac_src)))""",
    prettycode(fac_exp_anf))

    checkrun(s"""
    (let evalc         $evalc_src0
    (let fac_src       (quote $fac_src)

    ((run 0 (evalc fac_src)) 4)))""",
    "Cst(24)")

    checkcode(s"""
    (let evalc         $evalc_src1
    (let fac_src       (quote $fac_src)

    (evalc fac_src)))""",
    prettycode(fac_exp_anf))
  }
}
