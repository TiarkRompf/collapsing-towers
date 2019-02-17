object Matches {

import Base._
import Lisp._
import Lisp.parser._

val matches_poly_src = """(let matches (lambda matches n (lambda _ s
  (if (equs 'done (car n)) (maybe-lift 'yes)
    (if (equs (maybe-lift 'done) (car s)) (maybe-lift 'no)
      (if (equs (maybe-lift (car n)) (car s)) ((matches (cdr n)) (cdr s)) (maybe-lift 'no))))))
  (lambda _ n (maybe-lift (lambda _ s ((matches n) s)))))
"""

val matches_src = matches_poly_src.replace("maybe-lift", "nolift")
val matchesc_src = matches_poly_src.replace("maybe-lift", "lift")

val Success(matches_val, _) = parseAll(exp, matches_src)
val Success(matchesc_val, _) = parseAll(exp, matchesc_src)

val Success(ab_val, _) = parseAll(exp, """(a b done)""")
val Success(ac_val, _) = parseAll(exp, """(a c done)""")

val eval_exp = trans(eval_val,List("arg","arg2", "arg3"))
val evalc_exp = trans(evalc_val,List("arg","arg2", "arg3"))

val matches_ab_poly_src = s"""($matches_poly_src '(a b done))"""
val matches_ab_src = matches_ab_poly_src.replace("maybe-lift", "nolift")
val matchesc_ab_src = matches_ab_poly_src.replace("maybe-lift", "lift")

val Success(matches_ab_val, _) = parseAll(exp, matches_ab_src)
val Success(matchesc_ab_val, _) = parseAll(exp, matchesc_ab_src)

val matches_bis_poly_src = """
(let match_loop (lambda match_loop m (maybe-lift (lambda _ s
  (if (equs (maybe-lift 'yes) (m s))
      (maybe-lift 'yes)
      (if (equs (maybe-lift 'done) (car s))
          (maybe-lift 'no)
         ((match_loop m) (cdr s)))))))
(let star_loop (lambda star_loop m (lambda _ c (maybe-lift (lambda _ s
  (if (equs (maybe-lift 'yes) (m s))
      (maybe-lift 'yes)
      (if (equs (maybe-lift 'done) (car s))
          (maybe-lift 'no)
          (if (equs '_ c)
              (((star_loop m) c) (cdr s))
              (if (equs (maybe-lift c) (car s))
                 (((star_loop m) c) (cdr s))
                 (maybe-lift 'no)))))))))
(let match_here (lambda match_here r (lambda _ s
  (if (equs 'done (car r)) (maybe-lift 'yes)
  (let m (lambda _ s (if (equs '_ (car r))
 (if (equs (maybe-lift 'done) (car s))
                          (maybe-lift 'no)
                          ((match_here (cdr r)) (cdr s)))
  (if (equs (maybe-lift 'done) (car s))
                          (maybe-lift 'no)
                          (if (equs (maybe-lift (car r)) (car s))
                              ((match_here (cdr r)) (cdr s))
                              (maybe-lift 'no)))))
    (if (equs 'done (car (cdr r)))
        (if (equs '$ (car r))
            (if (equs (maybe-lift 'done) (car s))
                       (maybe-lift 'yes)
                       (maybe-lift 'no))
            (m s))
    (if (equs '* (car (cdr r)))
        (((star_loop (match_here (cdr (cdr r)))) (car r)) s)
        (m s)))))))
(let match (lambda match r
  (if (equs 'done (car r)) (maybe-lift (lambda _ s (maybe-lift 'yes)))
      (if (equs '^ (car r))
          (maybe-lift (match_here (cdr r)))
          (match_loop (match_here r)))))
match))))
"""

val matches_bis_src = matches_bis_poly_src.replace("maybe-lift", "nolift")
val matchesc_bis_src = matches_bis_poly_src.replace("maybe-lift", "lift")

val Success(matches_bis_val, _) = parseAll(exp, matches_bis_src)
val Success(matchesc_bis_val, _) = parseAll(exp, matchesc_bis_src)

val Success(a__val, _) = parseAll(exp, """(^ a _ $ done)""")

val Success(a__star_a_val, _) = parseAll(exp, """(a _ * a done)""")

val Success(a_bstar_a_val, _) = parseAll(exp, """(a b * a done)""")

val Success(a_bstar_a_tight_val, _) = parseAll(exp, """(^ a b * a $ done)""")

val Success(abba_val, _) = parseAll(exp, """(a b b a done)""")

val Success(abca_val, _) = parseAll(exp, """(a b c a done)""")

def testMatchesBis() = {
  println("// ------- test matches bis --------")
  def test1(re: Val, s: Val, b: Boolean, expected: String = "") = {
    val e = if (b) "Str(yes)" else "Str(no)"
    check(run { evalms(List(matches_bis_val, re, s),
      App(App(App(App(eval_exp,Var(0)),Sym("nil-env")),Var(1)), Var(2))
    )})(e)

    val d = reifyc { evalms(List(re,matchesc_bis_val,eval_val),App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0))) }
    if (expected != "")
      check(pretty(d, Nil))(expected)
    val r = run { val m = evalms(Nil,d); evalms(List(m, s), App(Var(0), Var(1))) }
    check(r)(e)
  }
  test1(ab_val, ab_val, true)
  test1(ab_val, ac_val, false)
  test1(ab_val, abba_val, true)
  test1(a__val, ab_val, true)
  test1(a__val, ac_val, true)
  test1(a__val, abba_val, false)
  test1(a_bstar_a_val, abba_val, true)
  test1(a_bstar_a_val, abca_val, false)
  test1(a__star_a_val, abba_val, true)
  test1(a__star_a_val, abca_val, true)

  val expected_a_bstar_a_tight = """
  |fun f0 x1 
  |  let x2 = x1._1 in 
  |  let x3 = "done" == x2 in 
  |  if (x3) "no" 
  |  else 
  |    let x4 = x1._1 in 
  |    let x5 = "a" == x4 in 
  |    if (x5) 
  |      let x6 = x1._2 in 
  |      let x7 = 
  |        fun f7 x8 
  |          let x9 = x8._1 in 
  |          let x10 = "done" == x9 in 
  |          let x11 = 
  |            if (x10) "no" 
  |            else 
  |              let x11 = x8._1 in 
  |              let x12 = "a" == x11 in 
  |              if (x12) 
  |                let x13 = x8._2 in 
  |                let x14 = x13._1 in 
  |                let x15 = "done" == x14 in 
  |                if (x15) "yes" 
  |                else "no" 
  |              else "no" in 
  |          let x12 = "yes" == x11 in 
  |          if (x12) "yes" 
  |          else 
  |            let x13 = x8._1 in 
  |            let x14 = "done" == x13 in 
  |            if (x14) "no" 
  |            else 
  |              let x15 = x8._1 in 
  |              let x16 = "b" == x15 in 
  |              if (x16) 
  |                let x17 = x8._2 in (f7 x17) 
  |              else "no" in (x7 x6) 
  |    else "no"""".stripMargin

  test1(a_bstar_a_tight_val, abba_val, true, expected_a_bstar_a_tight)
}

def testMatches() = {
println("// ------- test matches --------")
check(evalms(List(matches_val, ab_val, ac_val),App(App(App(App(eval_exp,Var(0)),Sym("nil-env")),Var(1)), Var(1))))("Str(yes)")
check(evalms(List(matches_val, ab_val, ac_val),App(App(App(App(eval_exp,Var(0)),Sym("nil-env")),Var(1)), Snd(Var(1)))))("Str(no)")
check(evalms(List(matches_val, ab_val, ac_val),App(App(App(App(eval_exp,Var(0)),Sym("nil-env")),Var(1)), Var(2))))("Str(no)")

// interpretation
check(run { evalms(List(ab_val,matches_val,eval_val), App(App(App(App(eval_exp,Var(1)),Sym("nil-env")),Var(0)),Var(0))) })("Str(yes)")

// double interpretation
check(run { evalms(List(ab_val,matches_val,eval_val), App(App(App(App(App(App(eval_exp,Var(2)),Sym("nil-env")), Var(1)), Sym("nil-env2")), Var(0)), Var(0))) })("Str(yes)")

// generation + interpretation
val c1 = reifyc { evalms(List(ab_val,matches_val,eval_val),App(App(evalc_exp,Var(1)),Sym("nil-env"))) }
//println(pretty(c1, Nil))
val r1 = run { val m = evalms(Nil,c1); evalms(List(m, ab_val), App(App(Var(0), Var(1)), Var(1))) }
check(r1)("Str(yes)")

// generation + generation + interpretation
val c2 = reifyc { evalms(List(ab_val,matchesc_val,eval_val),App(App(evalc_exp,Var(1)),Sym("nil-env"))) }
val d2 = reifyc { val m = evalms(Nil,c2); evalms(List(m, ab_val), App(Var(0), Var(1))) }
val expected = """
|fun f0 x1 
|  let x2 = x1._1 in 
|  let x3 = "done" == x2 in 
|  if (x3) "no" 
|  else 
|    let x4 = x1._1 in 
|    let x5 = "a" == x4 in 
|    if (x5) 
|      let x6 = x1._2 in 
|      let x7 = x6._1 in 
|      let x8 = "done" == x7 in 
|      if (x8) "no" 
|      else 
|        let x9 = x6._1 in 
|        let x10 = "b" == x9 in 
|        if (x10) 
|          let x11 = x6._2 in "yes" 
|        else "no" 
|    else "no"""".stripMargin
check(pretty(d2, Nil))(expected)
val r2 = run { val m = evalms(Nil,d2); evalms(List(m, ab_val), App(Var(0), Var(1))) }
val s2 = run { val m = evalms(Nil,d2); evalms(List(m, ac_val), App(Var(0), Var(1))) }
check(r2)("Str(yes)")
check(s2)("Str(no)")

// interpretation for generation
val c3 = run { evalms(List(ab_val,matchesc_val,eval_val),App(App(eval_exp,Var(1)),Sym("nil-env"))) }
val d3 = reifyc { evalms(List(c3, ab_val), App(Var(0), Var(1))) }
check(pretty(d3, Nil))(expected)

// "direct" generation
val d4 = reifyc { evalms(List(ab_val,matchesc_val,eval_val),App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0))) }
check(pretty(d4, Nil))(expected)

// different interpretation
val r5 = run { evalms(List(ab_val,matches_ab_val,eval_val),App(App(App(eval_exp,Var(1)),Sym("nil-env")), Var(0))) }
check(r5)("Str(yes)")

val d6 = reifyc { evalms(List(ab_val,matchesc_ab_val,eval_val),App(App(eval_exp,Var(1)),Sym("nil-env"))) }
check(pretty(d6, Nil))(expected)

// ----
// "direct" generation with modified semantics (count variable accesses)
val counter_cell = new Cell(Cst(0))
val d5 = reifyc { evalms(List(ab_val,matchesc_val,counter_cell),App(App(App(App(evalt_vc_exp, LiftRef(Var(2))),Var(1)),Sym("nil-env")), Var(0))) }
check(counter_cell.v)("Cst(0)")
//check(pretty(d5, Nil))(expected) 
val r6 = run { val m = evalms(Nil,d5); evalms(List(m, ab_val), App(Var(0), Var(1))) }
check(counter_cell.v)("Cst(8)")
counter_cell.v = Cst(0)
val s6 = run { val m = evalms(Nil,d5); evalms(List(m, ac_val), App(Var(0), Var(1))) }
check(counter_cell.v)("Cst(6)") // less accesses b/c early termination
check(r6)("Str(yes)")
check(s6)("Str(no)")


// TODO: generate a specialized regexp compiler that will generate code that counts var accesses!

}
}
