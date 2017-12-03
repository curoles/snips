//http://en.wikibooks.org/wiki/Microprocessor_Design/Add_and_Subtract_Blocks

/*
 *
 *              +-----+                       +------+
 *    a +----+--+ xor |    w1                 |xor   |   sum
 *           |  |     +-----------------------+      +--------+
 *    b +-+-----+     |                       |      |
 *        |  |  +-----+   +-------------------+      |
 *        |  |            |                   +------+
 *        |  |  +-----+   |
 *        |  +--+and  |   |                   +------+
 *        |     |     |   |      w2           | or   |
 *        +-----+     +-----------------------+      |
 *              +-----+   |                   |      |
 *                        |                   |      +--cout--+
 * cin +------------------+       a&cin  +----+      |
 *                                            |      |
 *                                b&cin  +----+      |
 *                                            +------+
 * 
 *  a b cin cout s
 *  0 0  0   0   0
 *  0 0  1   0   1
 *  0 1  0   0   1
 *  0 1  1   1   0
 *  1 0  0   0   1
 *  1 1  0   1   0
 *  1 1  1   1   1
 */
module FullAdder(
    input  a,
    input  b,
    input  cin,
    output cout,
    output sum
);

    wire w1, w2, w3, w4; // internal nets

    xor (w1, a, b); 
    xor (sum, w1, cin);
    and (w2, a, b);
    and (w3, a, cin);
    and (w4, b, cin);
    or  (cout, w2, w3, w4);

endmodule


