object TestMain {
  import Base._
  import Lisp._
  import Matches._

  def main(args: Array[String]) {
    //testBase()
    //testLisp()
    testPink()
    //benchmarks()
  }

  def benchmarks() {
    println("PINK BENCHMARKS")
    benchFac()
  }

  def testBase() {
    testBasic()
    testAck1()
    testAck2()
    testFac1()
  }

  def testLisp() {
    testEval()
    testEvalCps()
    testEvalAmb()

    testMutEval()
    testMutInEval()

    testEvalSyntax()

    testMatches()
    testMatchesBis()

    testUnstaging() // experimental
  }

  def testPink() {
    Pink.test()
    Pink_clambda.test()
    Pink_CPS.test()
    // disable Pink_macro by default because they require stack
    //Pink_macro.test()
  }
}
