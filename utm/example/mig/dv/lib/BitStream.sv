/**
 * @file
 * @brief  BitStream queue container.
 * @author Igor Lesik 2016
 *
 *
 * Queue-like abstract container template that can hold
 * any bit-packed data type. 
 * 
 *
 */

package BitStreamPkg;

    /// Class BitStream.
    /// Bit-stream queue of some data type.
    class BitStream #(type Data);
        localparam DATA_SIZE = $bits(Data);
        typedef bit [DATA_SIZE-1:0] Bits;
        Bits stream[$]; ///< the queue

        /// Push data into the queue.
        function void push(input Data d);
            push_bits(Bits'(d));
        endfunction

        /// Push raw bits into the queue.
        function void push_bits(input Bits d);
            stream = {stream, d}; // append
        endfunction

        /// Pop data from the queue.
        function Data pop();
            // convert stream back to a Data packet
            return Data'(pop_bits());
        endfunction

        /// Pop raw bits.
        function Bits pop_bits();
            automatic Bits d = stream[0]; // get first element
            stream = stream[1:$]; // remove packet from stream
            return d;
        endfunction

    endclass

    /// Function unittest, self-check unit test.
    ///
    function void unittest(bool verbose = false);

        typedef struct {
            uint16 address;
            reg [3:0] code;
            byte command [2];
        } Packet;
        automatic Packet q;
        automatic Packet p = Packet'{address:16'd7, code:4'd3, default: 0};
        automatic BitStream#(Packet) stream = new;
        stream.push(p);
        q = stream.pop();
        assert (q == p);

    endfunction

endpackage: BitStreamPkg
