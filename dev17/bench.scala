import org.scalameter._
object Bench {
  def bench(thunk: => Unit) = {    
    val time = measure {
      for (i <- 0 until 100000) {
        thunk
      }
    }
    time
  }
}
