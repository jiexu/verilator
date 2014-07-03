// ---------------------------------------------------------------------------
// this is used to test verilator
// ---------------------------------------------------------------------------


// ---------------------------------------------------------------------------
// Module under test
// ---------------------------------------------------------------------------
module t (clk);

input clk;

// ---------------------------------------------------------------------------
// signal declarion
// ---------------------------------------------------------------------------
logic [63:0] val = 64'h0123456789abcdef;
logic [127:0] tmp;
logic [127:0] tmpp;

integer cycles = 0;


// ---------------------------------------------------------------------------
// combinational blocks / continuous assignament
// ---------------------------------------------------------------------------
always_comb begin: b_test
    tmp  = 0;
    tmpp = 0;
    tmp[63:0]  = val;
    tmpp[63:0] = val;
    tmpp[63:0] = {tmp[0+:32], tmp[32+:32]};
    tmp[63:0]  = {tmp[0+:32], tmp[32+:32]};
end

// ---------------------------------------------------------------------------
// sequential blocks
// ---------------------------------------------------------------------------
always_ff @ (posedge clk)
begin
     // functional check part
     val <= val + 1; 


     if (tmp != tmpp)
     begin
          $display("%%Error: assignment wrong at %0d got=%x exp=%x", cycles, tmp, tmpp); 
          $stop;
     end


     // time controlling and finish part
     cycles <= cycles + 1; 
     if (cycles == 99) begin
          $write("*-* All Finished *-*\n");
          $finish;
     end
    
end

endmodule
