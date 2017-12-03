import scala.collection

object Functional {

    /** Memoization
     *
     *  Scala does not implement memoization directly but has a collection
     *  method named `getOrElseUpdate()` that handles most of the work
     *  of implementing it.
     *
     *  @param f function we want to optimize by re-using prev. results
     *  @return closure that checks internal cache before calling the function
     */
    def memoize[A, B](f: A => B) = new (A => B) {
        val cache = scala.collection.mutable.Map[A, B]()
        def apply(x: A) : B = cache.getOrElseUpdate(x, f(x))
    }

    /* TODO
    def memoize2[A, B, Mp: mutable.Map[A, B]] (f: A => B) = new (A => B) {
        val cache = new Mp()
        def apply(x: A) : B = cache.getOrElseUpdate(x, f(x))
    }*/

    // TODO experiment with WeakHashMap

    /** Returns new list by filtering elements of input list
     *
     *  @param xs input list
     */
    def myfilter(
        xs: List[Int],     // input list
        p:  Int => Boolean
    )
        : List[Int] =
    {
        if      (xs.isEmpty) xs
        else if (p(xs.head)) xs.head :: myfilter(xs.tail, p)
        else                 myfilter(xs.tail, p)
    }


}


import org.scalatest.FlatSpec

//scala -cp "./build/scala/class:./build/scala/extralib/*" org.scalatest.run  FunctionalSpec
//http://doc.scalatest.org/3.0.0/#org.scalatest.FlatSpec
//
class FunctionalSpec extends FlatSpec {

    it should "memoized function works as original" in {
        def incr(a: Int) = { a + 1 }
        def memoIncr = Functional.memoize(incr)
        assert(memoIncr(2) == 3)
        assert(memoIncr(2) == 3)
    }

    it should "return list with only even numbers" in {
        def isEven(n: Int) : Boolean = { n % 2 == 0 }
        assert(Functional.myfilter(List(1, 2, 3, 4), isEven) == List(2,4))
    }

}

