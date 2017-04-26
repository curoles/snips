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







 
