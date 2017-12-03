/** Text file IO and display helpers.
 *
 *  @author Igor Lesik 2016
 */


/** Text file IO and display helpers */
object TextFile {

  /** Read text file.
   *  @return text as String
   *  @example val text = TextFile.read(filename)
   */
  def read(fileName: String): String = {
    io.Source.fromFile(fileName).mkString
  }

  /** Lines as List of Strings */
  type Lines = List[String]

  /** Read all lines from text file.
   *  @return list of the lines
   *  @example
   *  {{{
   *  val lines = TextFile.readLines(filename)
   *  }}}
   */
  def readLines(fileName: String): Lines = {
    io.Source.fromFile(fileName).getLines().toList
  }

  /** Line as tuple(string, lineNumber) */
  type NumberedLine = (String, Int)

  /** Lines as List of tuples(string, lineNumber) */
  type NumberedLines = List[NumberedLine]

  /** Convert list of lines to list of lines with line numbers */
  def toNumberedLines(lines: Lines): NumberedLines = {
    lines.zipWithIndex
  }

  /** Read lines from file */
  def readNumberedLines(fileName: String) =
    toNumberedLines(readLines(fileName))

  /** Find longest line in the list of lines.
   *  @param lines list of lines
   *  @return copy of the longest string in the list
   */
  def findLongestLine(lines: Lines) = lines.reduceLeft(
    (a, b) => if (a.length > b.length) a else b
  )

  /** Make line prefix string as "nn | " where nn is line number.
   *  Like line numbers we see in a text editor.
   *  Works on lines that already coupled with line number.
   */
  def makeLineNumPads(lines: NumberedLines, terminal: String = " | "): Lines = {
    def numStrWidth(ln: NumberedLine) = ln._2.toString.length
    val longestNumStr = lines.reduceLeft((a, b) => if (numStrWidth(a) > numStrWidth(b)) a else b)
    val maxWidth = numStrWidth(longestNumStr)
    lines.map(ln => (" " * (maxWidth-numStrWidth(ln))) + ln._2.toString + terminal)
  }

  def lineNumPads(lines: Lines, terminal: String = " | "): Lines = {
    makeLineNumPads(toNumberedLines(lines), terminal)
  }

  /** Couple line string and line padding string */
  def zipWithPads(lines: Lines, pads: Lines): List[(String, String)] = {
    lines.zip(pads)
  }

  /** Concatenate lines and pads and form the text */
  def toLineNumPaddedText(lines: Lines): String = {
    val paddedLines = zipWithPads(lines, lineNumPads(lines))
    paddedLines.map(line_pad => line_pad._2 + line_pad._1).mkString("\n")
  }


  /**
   *
   *  @example
   *  {{{
   *  scala> val lines = TextFile.readLines("src/scala/TextFile.scala")
   *  scala> val (lc,wc) = TextFile.wordCount(lines)
   *  lc: Int = 87
   *  wc: Int = 475
   *  }}}
   */
  def wordCount(lines: Lines): (Int, Int) = {
    val lc: Int = lines.length
    val wc: Int = lines.map(ln => ln.split("[ ,!.]+").length).fold(0) {(a,b) => a + b}
    (lc, wc)
  }
}
