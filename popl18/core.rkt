#lang racket
(require redex)
(provide (all-defined-out))

(define-language vm
  (e x (lit number) (str string) (lam f x e) (cons e e) (code e) (let x e e) (app e e) (if e e e) (a e) (b e e) (lift e) (run e e)
     (reflect e) (lamc f x e) (letc x e e))
  (v (lit number) (str string) (lam f x e) (cons v v) (code e))
  (a car cdr isLit isStr isCons)
  (b plus minus times eq)
  (E hole (cons E e) (cons v E) (let x E e) (app E e) (app v E) (if E e e) (a E) (b E e) (b v E) (lift E) (run E e) (reflect E))
  (M hole
     (cons M e) (cons v M) (let x M e) (app M e) (app v M) (if M e e) (a M) (b M e) (b v M) (lift M) (run M e) (reflect M)
     (lift (lamc f x M)) (if (code e) M e) (if (code e) v M) (run v M) (letc x e M))
  (R (cons R e) (cons v R) (let x R e) (app R e) (app v R) (if R e e) (a R) (b R e) (b v R) (lift R) (run R e) (reflect R)
     (lift (lamc f x P)) (if (code e) P e) (if (code e) v P) (run v P) (letc x e P))
  (P hole
     (cons R e) (cons v R) (let x R e) (app R e) (app v R) (if R e e) (a R) (b R e) (b v R) (fix R) (lift R) (run R e) (reflect R)
     (lift (lamc f x P)) (if (code e) P e) (if (code e) v P) (run v P) (letc x e P))
  (x (variable-except lit str lam cons let app if car cdr isLit isStr isCons plus minus times eq lift run reflect letc code))
  (f x))

(define not-code? (lambda (x) (not ((redex-match vm (code e)) x))))
(define no-reflect? (lambda (x) (not ((redex-match vm (in-hole E (reflect any))) x))))

(define red
  (reduction-relation
   vm
   (--> (in-hole M (let x v e))                 (in-hole M (subst x v e)) "let")
   (--> (in-hole M (app (lam f x e) v))         (in-hole M (subst x v (subst f (lam f x e) e))) "beta")
   (--> (in-hole M (if (lit 0) e_1 e_2))        (in-hole M e_2)           "if0")
   (--> (in-hole M (if (lit number_0) e_1 e_2)) (in-hole M e_1)           "ifn"
        (side-condition (not (= 0 (term number_0)))))
   (--> (in-hole M (car (cons v_1 v_2))) (in-hole M v_1)                  "car")
   (--> (in-hole M (cdr (cons v_1 v_2))) (in-hole M v_2)                  "cdr")
   (--> (in-hole M (isLit (lit number))) (in-hole M (lit 1))              "isLit1")
   (--> (in-hole M (isLit v)) (in-hole M (lit 0))                         "isLit0"
        (side-condition (and (not-code? (term v)) (not ((redex-match vm (lit number)) (term v))))))
   (--> (in-hole M (isStr (str string))) (in-hole M (lit 1))              "isStr1")
   (--> (in-hole M (isStr v)) (in-hole M (lit 0))                         "isStr0"
        (side-condition (and (not-code? (term v)) (not ((redex-match vm (str string)) (term v))))))
   (--> (in-hole M (isCons (cons v_1 v_2))) (in-hole M (lit 1))           "isCons1")
   (--> (in-hole M (isCons v)) (in-hole M (lit 0))                         "isCons0"
        (side-condition (and (not-code? (term v)) (not ((redex-match vm (cons e_1 e_2)) (term v))))))
   (--> (in-hole M (plus (lit number_1) (lit number_2)))
        (in-hole M (lit ,(+ (term number_1) (term number_2))))             "plus")
   (--> (in-hole M (minus (lit number_1) (lit number_2)))
        (in-hole M (lit ,(- (term number_1) (term number_2))))             "minus")
   (--> (in-hole M (times (lit number_1) (lit number_2)))
        (in-hole M (lit ,(* (term number_1) (term number_2))))             "times")
   (--> (in-hole M (eq v_1 v_2))
        (in-hole M (lit ,(if (equal? (term v_1) (term v_2)) 1 0)))         "eq"
        (side-condition (and (not-code? (term v_1)) (not-code? (term v_2)))))
   (--> (in-hole M (if (code e_0) (code e_1) (code e_2)))
        (in-hole M (reflect (code (if e_0 e_1 e_2))))                     "ifccc")
   (--> (in-hole M (a_0 (code e_1)))
        (in-hole M (reflect (code (a_0 e_1))))                            "ac")
   (--> (in-hole M (b_0 (code e_1) (code e_2)))
        (in-hole M (reflect (code (b_0 e_1 e_2))))                        "bc")
   (--> (in-hole M (app (code e_1) (code e_2)))
        (in-hole M (reflect (code (app e_1 e_2))))                        "appc")
   (--> (in-hole M (lift (lit number_1)))
        (in-hole M (code (lit number_1)))                                 "lift-lit")
   (--> (in-hole M (lift (str string_1)))
        (in-hole M (code (str string_1)))                                 "lift-str")
   (--> (in-hole M (lift (cons (code e_1) (code e_2))))
        (in-hole M (reflect (code (cons e_1 e_2))))                       "lift-cons")
   (--> (in-hole M (lift (code e))) (in-hole M (reflect (code (lift e)))) "lift-code")
   (--> (in-hole M (lift (lamc f x (code e))))
        (in-hole M (reflect (code (lam f x e))))                          "lift-lamc")
   (--> (in-hole M (lift (lam f x e)))
        (in-hole M (lift (lamc f x (subst x (code x) (subst f (code f) e))))) "lift-lam")
   (--> (in-hole M (run (code e_1) (code e_2)))
        (in-hole M (reflect (code (run e_1 e_2))))                        "runcc")
   (--> (in-hole M (run v_1 (code e_2)))
        (in-hole M e_2)                                                   "runnc"
        (side-condition (not-code? (term v_1))))
   (--> (in-hole P (in-hole E (reflect (code e))))
        (in-hole P (letc x_new e (in-hole E (code x_new))))               "reify-reflect"
        (where x_new ,(variable-not-in (term (P E e)) (term x))))
   (--> (in-hole M (letc x_1 e_1 (code e_2)))
        (in-hole M (code (let x_1 e_1 e_2)))                              "letc")
   ))

(define-metafunction vm
  subst : x any any -> any
  [(subst x_1 any_1 (lam f x_1 any_2)) (lam f x_1 any_2)]
  [(subst f   any_1 (lam f x_1 any_2)) (lam f x_1 any_2)]
  [(subst x_1 any_1 (lam f x_2 any_2))
   (lam f_new x_new (subst x_1 any_1 (subst-var x_2 x_new (subst-var f f_new any_2))))
   (where x_new ,(variable-not-in (term (x_1 any_1 any_2)) (term x_2)))
   (where f_new ,(variable-not-in (term (x_1 any_1 any_2)) (term f)))]
  [(subst x_1 any_1 (let x_1 any_x any_2)) (let x_1 (subst x_1 any_1 any_x) any_2)]
  [(subst x_1 any_1 (let x_2 any_x any_2))
   (let x_new (subst x_1 any_1 any_x) (subst x_1 any_1 (subst-var x_2 x_new any_2)))
   (where x_new ,(variable-not-in (term (x_1 any_1 any_2)) (term x_2)))]
  [(subst x_1 any_1 (letc x_1 any_x any_2)) (letc x_1 (subst x_1 any_1 any_x) any_2)]
  [(subst x_1 any_1 (letc x_2 any_x any_2))
   (letc x_new (subst x_1 any_1 any_x) (subst x_1 any_1 (subst-var x_2 x_new any_2)))
   (where x_new ,(variable-not-in (term (x_1 any_1 any_2)) (term x_2)))]
  [(subst x_1 any_1 x_1) any_1]
  [(subst x_1 any_1 x_2) x_2]
  [(subst x_1 any_1 (any_2 ...))
   ((subst x_1 any_1 any_2) ...)]
  [(subst x_1 any_1 any_2) any_2])

(define-metafunction vm
  subst-var : x any any -> any
  [(subst-var x_1 any_1 x_1) any_1]
  [(subst-var x_1 any_1 (any_2 ...))
   ((subst-var x_1 any_1 any_2) ...)]
  [(subst-var x_1 any_1 any_2) any_2])
