import akka.actor._
import akka.util.Timeout
import akka.pattern.ask
import scala.concurrent.Await
import scala.concurrent.duration._
import scala.annotation.tailrec

object BattleFieldGame extends App {

    val system = ActorSystem("BattleField")

    val player1 = system.actorOf(Props[Player], "player1")
    val player2 = system.actorOf(Props[Player], "player2")
    val engine = system.actorOf(Props[GameEngine], "gameEngine")
    val player1UI = system.actorOf(Props[PlayerConsoleUI], "player1UI")

    val actorList = List(player1, player2, engine)

    implicit val timeout = Timeout(1.seconds)
    //val player1UIFuture = player1UI ? isDone()
    //val gameEngineFuture = engine ? isDone()


    @tailrec def checkEndOfGame(): Unit = {
        //val isPlayer1UIDone = Await.result(player1UI ? isDone(), timeout.duration)
        //val isGameEngineDone = Await.result(engine ? isDone(), timeout.duration)
        //val doneConds = List(isPlayer1UIDone, isGameEngineDone)
        val doneConds = actorList.map(x => Await.result(x ? isDone(), timeout.duration))
        val isEndOfGame = Done(doneConds.foldLeft(false)(
                               (r,c) => r || (c match {case Done(false) => false; case _ => true}) ))
        isEndOfGame match {
            case Done(false) => checkEndOfGame()
            case Done(true) => println("game is over")
        }
    }

    player1UI ! EnableConsole()

    checkEndOfGame()

    system.terminate()
    println("game terminated")
}

case class isDone()
case class Done(status: Boolean)

case class Strike()
case class Struck(x: Int, y: Int)
case class Report(x: Int, y: Int)

class Player extends Actor {

    def receive = {
        case Strike() =>
            println(s"strike")

        case Struck(x,y) =>
            println(s"struck $x:$y")

        case Report(x,y) =>
            sender ! Cell(x, y, struck = true, false)

        case isDone() =>
            //println("Is Player Done?")
            sender ! Done(false)

        case Done(status) =>
            println("Them say I am done!")

        case textMessage: String =>
            println(s"Text message: $textMessage")

    }
}

case class Cell(x: Int, y: Int, struck: Boolean, ship: Boolean)

class GameEngine extends Actor {

    var moveCount = 0


    def receive = {
        case isDone() =>
            //println(s"move=$moveCount, Is Game Engine Done?")
            //moveCount += 1
            sender ! Done(moveCount > 200)

        case message =>
            println(s"message $message")
    }

}

//https://searler.github.io/scala/akka/camel/reactive/2015/01/11/Simple-Akka-Stream-Camel-Integration.html
//http://stackoverflow.com/questions/7400784/how-to-get-actor-messages-from-stdin
//import akka.camel.{CamelMessage, CamelServiceManager, Consumer}
//http://sdanzig.blogspot.com/2013/06/buddychat-simple-example-of-akka-actors.html

case class EnableConsole()

class PlayerConsoleUI extends Actor {

    def receive = {
        case EnableConsole() =>
            println("enabling console")
            acceptUserInput()
            //sender ! Done(false)
            //context.actorSelection("../player1") ! Done(true)

    }

    def acceptUserInput() = {
        println("type something")
        for (ln <- (io.Source.stdin.getLines.takeWhile(!_.equals("done")))) {
             //log.debug("Line = {}", ln)
             //context.parent ! MessageFromConsole(ln)
             context.actorSelection("../player1") ! s"line:$ln"
        }
        //context.parent ! MessageFromConsole("done")
    }
}
