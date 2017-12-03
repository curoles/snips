//https://github.com/ktoso/scala-words/blob/master/src/main/scala/pl/project13/scala/words/nouns/PercentageNoun.scala

case class Percentage(part: Long) {

  def percent(max: Long): Long = if(max == 0) 0 else part * 100 / max
  def percentString(max: Long): String = (percent(max) + "%").toString

}

