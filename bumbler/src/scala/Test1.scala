//scala -cp "./build/scala/class:./build/scala/extralib/*" Test1

//import org.scalatest._

import scala.annotation.tailrec
import Weather._

object Test1 {

class C1 {
    def wow() = println("wow")
}

val c1 = new C1

import c1.wow

    def main(args: Array[String]): Unit = {
        println("Hello, worldsssssssss!")
        println(f"Pi=${math.Pi}%.5f")
        wow
        Weather.report("12770744")
        for (file <- io.Dir.list()) println(file)
        for (line <- io.Dir.grep(".*bumbler.*")) println(line)

        val file = new java.io.File("1.txt")

        io.FileTool.withPrintWriter(file) {
            writer => writer.println(new java.util.Date)
        }
    }


}


