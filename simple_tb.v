`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11/27/2025 02:44:02 PM
// Design Name: 
// Module Name: simple_tb
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

`define REG_SIZE 31

module simple_tb;
  reg  clock_proc;
  reg  rst;
  wire halt;
  wire [`REG_SIZE:0] trace_writeback_pc;
  wire [`REG_SIZE:0] trace_writeback_inst;
  
  
  parameter CLK_PERIOD = 20;          
  parameter HALF_PERIOD = CLK_PERIOD / 2; 
  Processor uut (
      .clk(clock_proc),
      .rst(rst),
      .halt(halt),
      .trace_writeback_pc (trace_writeback_pc) ,
      .trace_writeback_inst (trace_writeback_inst)
  );
  
  initial begin
      clock_proc = 1; 
      forever #HALF_PERIOD clock_proc = ~clock_proc;
  end

  initial begin
    rst = 1;
    // Giữ reset trong 2 chu kỳ
    repeat (2) @(negedge clock_proc);
    rst = 0;
    
    $display("TB: Reset = 0. Run program");
    wait (halt == 1);
    
    // Đã halt
    $display("TB: HALT = 1. Finished");
    $finish;
  end

endmodule
