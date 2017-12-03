
module Dve();

    reg  d;
    wire q;
    reg  clk;
    reg  rst;

    bind Dff Dff_checker #(.WIDTH(1)) dff_checker(.d(d), .q(q), .clk(clk));

    Dff #(.WIDTH(1)) dff(.d(d), .q(q), .clk(clk));

    initial
    begin

        $monitor("%d rst:%h clk:%h D:%h Q:%h", 
            $time, rst, clk, d, q);

        clk = 1'b0;
        d   = 1'b0;
        rst = 1'b1;

        repeat(2) @(posedge clk);
        rst = 1'b0;

        @(posedge clk);
        @(negedge clk);
        assert (q == d);

        d = 1;
        @(posedge clk);
        @(negedge clk);
        assert (q == d) $display ("OK. Q equals D");
        else $fatal(1/*"q != d"*/);

        d = 0; 
        repeat(5) begin
            @(posedge clk);
            d = ~d;
        end

        $finish();
    end

    always
    begin
        #1 clk = ~clk;
    end

endmodule: Dve
