script file
===========

```
#!/usr/bin/env scala
```
vs
```
#!/bin/sh
exec scala "$0" "$@"
!#
```
vs
```
#!/bin/bash
scala $0 $@
exit
!#
```

immutability
============
```
val a = new A
```
a is entirely immutable iff class A is immutable

entire immutability = immutable reference + immutable state

immutable class
===============
* all fields are val
* methods allow to read only, no change to state

function parentheses
====================
can drop if 0|1 parameters

foreach vs for
=============
(1 to 3).foreach(i => ...)

return multiple values
======================
as tuple
val (v1, v2, v3) = fun(...)
val v = fun(...); v._1, v._2

implicit parameters
===================
def fun(args)(implicit v: A)

caller:
implicit val(def?) iv = new A(...)
val av = new A
fun(...) //use implicit
fun(...)(av)

raw string """ for reg expr """
===============================
can use \ instead of \\

eq vs '=='
========
'==' value-based comparison (Javas methos equals)
eq identity-based comparison


semicolon val v = new A...; {}
==============================


aux constructor
==============
first statement must be call to primary|aux constructor

init var to def value
=====================
var s: String = _


method overriding requires override keyword
===========================================

only primary constructor calls base ctor
=========================================
primary ctor acts as the gateway to init an instance of a class


# Map getOrElseUpdate

```
object MarkerFactory {
  private val markers = Map(
    "red" -> new Marker("red"),
    "blue" -> new Marker("blue"),
    ...

  def getMarker(color: String) =
    markers.getOrElseUpdate(color, new Marker(color))
}
```

# private primary ctor
```
class Marker private(val color: String){...}
```

# companion class and companion object
can access everything of each other

# pool of instances
```
class Marker private(val color: String){...}

object Marker {
  private val markers = Map(
    "red" -> new Marker("red"),
    "blue" -> new Marker("blue"),
    ...

  def getMarker(color: String) =
    markers.getOrElseUpdate(color, new Marker(color))
}

```

# class-level operations

```
class Marker private(val color: String){
  override def toString = s"marker color $color"
}

object Marker {
  private val markers = Map(
    "red" -> new Marker("red"),
    "blue" -> new Marker("blue"),
    ...

  def getMarker(color: String) =
    markers.getOrElseUpdate(color, new Marker(color))a

  def apply(color: String) = getMarker(color) // to use like Marker("red")

  def supportedColors = markers.keys
}

```

# enumerations
```
object Color extends Enumeration {
  type Color = Value // for compiler to treat Color as type instead of an instance
  val RED, GREEN, BLUE = Value
}

class A(val clr: Color, ...

Color.values.foreach {clr => println(clr)}
```

# package object
```
//File aaa/bbb/package.scala
package aaa

package object bbb {
  def fun(...){}
}

//File aaa/bbb/Ccc.scala
package aaa.bbb

...
  fun(...)

# importing a package auto imports corresponding package object

trick to do in package object: type List[T] = scala.collection.immutable.List[T]
```

# Option type forces to check result "!=null"
```
def fun ... {
  if () Some("good") else None
}
val res = fun(...)
val a = res.getOrElse("oops")
```

# Loan Pattern
```
import java._io

def writeToFile(fileName: String)(codeBlock: PrinterWriter => Unit) {
  val writer = new PrintWriter(new File(fileName))
  try { codeBlock(writer) }
  finally { writer.close() }
}
```

```
writeToFile("output.txt") { writer =>
  writer write "hello from Me"
}
```

# Execute Around Method Pattern (Code Sandwich)

To clean up (free/unlock) a resource automatically after using it.
https://gist.github.com/dpsoft/9013481
http://pages.cs.wisc.edu/~liblit/tr-1647/
http://java-design-patterns.com/patterns/execute-around/

```
class Resource private() {
  println("starting transaction...")
  private def cleanUp() { ... }
  def op1() = ...
  def op2() = ...
  def op3() = ...
}

object Resource {
  def use(codeBlock: Resource => Unit) {
    val resource = new Resource
    try {
        codeBlock(resource)
    }
    finally {
        resource.cleanUp()
    }
  }
}
```

```
Resource.use { resource =>
  resource.op1()
  resource.op3()
  resource.op2()
}
```
