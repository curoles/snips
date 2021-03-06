// Inspiration from book Pragmatic Scala

import akka.actor._
import java.io._

case class ExploreDir(dirName:String)
case class ExploreFile(fileName:String)
case class DoneExploringDir(dirName:String)

class FileExplorer extends Actor {

    def receive = {
        case ExploreDir(dirName) =>
            val dir = new File(dirName)
            val children = dir.listFiles()
            if (children != null) {
                children.filter{_.isDirectory}.foreach{subDir => sender ! ExploreDir(subDir.getAbsolutePath)}
                children.filter{!_.isDirectory}.foreach{file => sender ! ExploreFile(file.getAbsolutePath)}
            }
            sender ! DoneExploringDir(dirName)
    }
}

import akka.routing._

class FilesExplorer extends Actor {
    val startTime = System.nanoTime
    var pending = 0

    val fileExplorers = context.actorOf(
        RoundRobinPool(32).props(Props[FileExplorer])
    )

    def receive = {
        case ExploreDir(dirName) =>
            pending += 1
            fileExplorers ! ExploreDir(dirName)

        case DoneExploringDir(dirName) =>
            doDirAction(dirName)
            pending -= 1
            if (pending == 0) {
                val endTime = System.nanoTime
                println(s"Time taken: ${(endTime - startTime)/1.0e9} seconds")
                context.system.terminate()
            }

        case ExploreFile(fileName) =>
            doFileAction(fileName)

        case msg =>
            println(s"unexpected message: $msg")
    }

    def doDirAction(dirName: String) = {
        println(s"directory: ${dirName}")
    }

    def doFileAction(fileName: String) = {
        println(s"file: ${fileName}")
    }

}

object ListFiles extends App {
    val system = ActorSystem("ls")
    val ls = system.actorOf(Props[FilesExplorer])
    ls ! ExploreDir(args(0))
}
