`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: Pennsylvania State University
// Engineer: Siddharth Shah
// 
// Create Date: 12/09/2023 05:27:29 PM
// Module Name: Testbench
//////////////////////////////////////////////////////////////////////////////////


module TestBench;

    // Inputs
    reg clk;
    // Add other input signals here

    // Outputs
    wire [31:0] pc;
    wire [31:0] dinstOut;
    initial begin
        clk <= 1'b0;
    end

Datapath datapath(
    .clk(clk), 
    .pc(pc), 
    .dinstOut(dinstOut) 
    );
    

    // Clock generation
    always begin
        #10;
        clk = ~clk;
    end

endmodule

