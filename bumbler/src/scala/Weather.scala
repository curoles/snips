import scala.xml._
import java.net._
import scala.io.Source

object Weather {

    def yahooWeatherUrl(zipCode: String) =
        //"http://xml.weather.yahoo.com/forecastrss?w="+zipCode+"&u=f"
"https://query.yahooapis.com/v1/public/yql?q=select%20*%20from%20weather.forecast%20where%20woeid%20in%20(select%20woeid%20from%20geo.places(1)%20where%20text%3D%22nome%2C%20ak%22)&format=xml&env=store%3A%2F%2Fdatatables.org%2Falltableswithkeys"

    def xmlReportString(url: String) : String = {
        Source.fromURL(new URL(url)).mkString
    }

    def xmlReportFromString(xmlString: String) = XML.loadString(xmlString)

    def xmlReport(zipCode: String) =
        xmlReportFromString(xmlReportString(yahooWeatherUrl(zipCode)))

    def report(zipCode: String) : List[String] = {
        val xml = xmlReport(zipCode)
        val city  = xml \\ "location" \\ "@city"
        val state = xml \\ "location" \\ "@region"
        val temp  = xml \\ "condition" \\ "@temp"
        println(city + ", " + state + " " + temp)
        List(state.toString, city.toString, temp.toString)
    }
}
