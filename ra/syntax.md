#<center>Syntax</center>

## Identifiers

Allowed symbols:

- letters
- digits
- underscore `'_'`
- accent ``'`'``

Examples:

    i_am_variable
    i`am`variable`too


## Literals

### String literals

    "I am string literal"

### Numeric literals

    \d*[d|i|u|h|x|b]\d* or \d*`.*`

- decimal

        123
        0d123, 0i123 - signed decimal integer
        0u123 - unsigned decimal integer
        32u123 - 32-bit unsigned decimal integer

- hexadecimal

        0hff
        0xdead_beef
        16xdead - 16-bit number

- binary

        0b01
        8b0101_0101 - 8-bit binary number

- ASCII 7-bit character

        0`a`
        0`\n`

## Functions

    def double(x : Int) : Int { x * 2 }
    def double'T'(x : T) : T { x * 2 }

    val n10 = double(5);
    val n10 = 5.double;

    val n10 = double'Int'(5);

    val x2 ~ double'Int'; val n10 = x2(5);

    def double(val x : Int) : Int { x = x * 2 } // compilation error, x is immutable (default)
    def double(var x : Int) : Int { x = x * 2 } // ok

## If else

    if expr then { if-arm } else { else-arm }
    var res : Bool = if expr then { if-arm } else { else-arm }

