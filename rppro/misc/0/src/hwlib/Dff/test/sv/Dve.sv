
module Dve();

    reg  d;
    wire q;
    reg  clk;

    Dff #(.WIDTH(1)) dff(.d(d), .q(q), .clk(clk));

    //assert property (@(negedge clk) (q == d));

    initial
    begin

        $monitor("%d clk:%h D:%h Q:%h", 
            $time, clk, d, q);

        clk = 1'b0;
        d   = 1'b0;

        @(posedge clk);
        @(negedge clk);
        assert (q == d);

        d = 1;
        @(posedge clk);
        @(negedge clk);
        assert (q == d) $display ("OK. Q equals D");
        else $error("oops");

        $finish();
    end

    always
    begin
        #1 clk = ~clk;
    end

endmodule: Dve
