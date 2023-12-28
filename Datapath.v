`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: Pennsylvania State University
// Engineer: Siddharth Shah
// 
// Create Date: 12/09/2023 04:34:32 PM
// Module Name: datapath
//////////////////////////////////////////////////////////////////////////////////
module ProgramCounter(
    input clk,            // Clock input necessary as PC only updates on the positive edge of the clock.
    input [31:0] nextPc, // Input from the PC adder looped back to update the next PC.
    
    //final project input
    input wpcir,
    
    output reg [31:0] pc // Output of the PC module.
    
);

initial
    begin
        pc = 32'd100;      // Initializing the PC value to start at 100 in decimal.
    end

always @(posedge clk)
    begin
      if (wpcir == 1)
        pc = nextPc;      // Update PC to be nextPc only on the positive edge of the clock.
    end

endmodule

module pcAdder( //creation of the module used for the PC adder module in the cpu.
    input [31:0] pc, //input of pc set to be 32 bits wide.
    output reg [31:0] nextPc //output register of next pc that is also 32 bits wide.
);

    always @(*) begin //always block that changes ony any signal used to continually update nextPc.
        nextPc <= pc + 32'b00000000000000000000000000000100; //setting nextPc equal to ithe input of pc plus a unsigned binary 32 bit 4.
    end //end always block

endmodule

module InstructionMemory( //instruction memory module within the cpu.
    input [31:0] pc, //input of the instruction memory module.
    output reg [31:0] instOut //instruction output of the memory module
    );
       reg [31:0] memory [0:63]; //32x64 array used to store instructions to memory.
       
       initial begin
        //final project instructions
            // add $3, $1, $2
                memory[25] = {6'b000000, 5'b00001, 5'b00010, 5'b00011, 5'b00000, 6'b100000};
            // sub $4, $9, $3
                memory[26] = {6'b000000, 5'b01001, 5'b00011, 5'b00100, 5'b00000, 6'b100010};
            // or $5, $3, $9
                memory[27] = {6'b000000, 5'b00011, 5'b01001, 5'b00101, 5'b00000, 6'b100101};
            // xor $6, $3, $9
                memory[28] = {6'b000000, 5'b00011, 5'b01001, 5'b00110, 5'b00000, 6'b100110};
            // and $7, $3, $9
                memory[29] = {6'b000000, 5'b00011, 5'b01001, 5'b00111, 5'b00000, 6'b100100};
end
    always @ (*) //always block to update instruction out setting to the memory array of pc bits 7 to 2. 
        begin
            instOut <= memory[pc[7:2]];
        end
endmodule

module IFIDpipelineReg( //IFID pipeline
    input clk, //clock input needed as dinstOut only updates on the positive edge of clock.
    input [31:0] instOut, //input
    
    //final project input
    input wpcir,
    
    output reg [31:0] dinstOut //output
    );
    
    always @ (posedge clk) //always block that will only update dinstOut on the positive edge of the clock. dinstOut is to the instOut input of this module.
        begin
         if (wpcir == 1)
            dinstOut <= instOut;
        end
        
endmodule

module ControlUnit( //control unit module of the cpu
    //inputs
    input [5:0] op,
    input [5:0] func,
    
    //final project inputs
    input [4:0] rs, 
    input [4:0] rt,
    input [4:0] mdestReg,
    input mm2reg,
    input mwreg,
    input [4:0] edestReg,
    input em2reg,
    input ewreg,
    
    //outputs
    output reg wreg,
    output reg m2reg,
    output reg wmem,
    output reg [3:0] aluc,
    output reg aluimm,
    output reg regrt,
    
    //final project outputs
    output reg [1:0] fwda,
    output reg [1:0] fwdb,
    output reg wpcir
    
    );
    
    reg regUsage = 1'b1;
	
    initial begin  
	    wreg <= 0; //RegWrite  
	    m2reg <= 0; //Mem2Reg  
        wmem <= 0; //Write Memory  
        aluimm <= 0; //ALU source  
        regrt <= 0; //Reg Destination  
	end  
	
    always @ (*) begin //always block that will continually update    
        case (op) //case statement of the op code portion of dinstOut which is connected in the datapath module. 
            6'b000000: // R-type instructions
            begin
                  wreg = 1'b1; // Write to the register file
                  m2reg = 1'b0; // Do not write to memory
                  wmem = 1'b0; // Do not write to memory
                  aluimm = 1'b0; // ALU source from registers
                  regrt = 1'b0; // Destination register address 

                case (func) //case statement to check which operation is performed.
                    6'b100000: aluc = 4'b0010; //ADD Operation
                    6'b100010: aluc = 4'b0110; //SUB Operation
                    6'b100100: aluc = 4'b0000; //AND Operation
                    6'b100101: aluc = 4'b0001; //OR Operation
                    6'b100110: aluc = 4'b0011; //XOR Operation
                    default: // Default behavior for unspecified func values
                    begin
                        
                        wreg = 1'b0;
                        m2reg = 1'b0;
                        wmem = 1'b0;
                        aluc = 4'b0000;
                        aluimm = 1'b0;
                        regrt = 1'b0;
                    end
                endcase
            end
            6'b100011: // LW instruction
            begin
                // Set control signals for LW instruction
                wreg = 1'b1; // Write to the register file
                m2reg = 1'b1; // Write to memory
                wmem = 1'b0; // Do not write to memory
                aluc = 4'b0010; // ALU operation for addition
                aluimm = 1'b1; // ALU source from registers
                regrt = 1'b1; // Destination register address
            end
          6'b101011: //SW instruction
            begin
                wreg = 1'b0;
                m2reg = 1'b0;
                wmem = 1'b1;
                aluc = 4'b0010;
                aluimm = 1'b1;
                regrt = 1'b1; 
            end 
            default: // Default behavior for unspecified op values
            begin
                
                wreg = 1'b0;
                m2reg = 1'b0;
                wmem = 1'b0;
                aluc = 4'b0000;
                aluimm = 1'b0;
                regrt = 1'b0;
            end
        endcase
    end
    
    
//stall
    always @ (*) 
        begin
            if ((ewreg == 1'b1) && (em2reg == 1'b1) && (edestReg != 5'b0) && (regUsage == 1'b1)
            && ((edestReg == rs) || (edestReg == rt))) begin
                wreg = 1'b0;
                wmem = 1'b0;
                wpcir = 1'b0;
            end 
            else begin
                wpcir = 1'b1;
            end
// forwarding
            if ((ewreg == 1'b1) && (edestReg != 5'b0) && (edestReg == rs) && (em2reg == 1'b0)) begin
                fwda = 2'b01;
        end
            else if ((mwreg == 1'b1) && (mdestReg != 5'b0) && (mdestReg == rs) && (mm2reg == 1'b0)) begin
                fwda = 2'b10;
        end
            else if ((mwreg == 1'b1) && (mdestReg != 5'b0) && (mdestReg == rs) && (mm2reg == 1'b1)) begin
                fwda = 2'b11;
        end
            else begin
                fwda = 2'b00;
        end
            if ((ewreg == 1'b1) && (edestReg != 5'b0) && (edestReg == rt) && (em2reg == 1'b0)) begin
                fwdb = 2'b01;
        end
            else if ((mwreg == 1'b1) && (mdestReg != 5'b0) && (mdestReg == rt) && (mm2reg == 1'b0)) begin
                fwdb = 2'b10;
        end
            else if ((mwreg == 1'b1) && (mdestReg != 5'b0) && (mdestReg == rt) && (mm2reg == 1'b1)) begin
                fwdb = 2'b11;
        end
            else begin
                fwdb = 2'b00;
            end
        end

endmodule

module RegrtMultiplexer(
    // Inputs
    input [4:0] rt,     
    input [4:0] rd,     
    input regrt,        

    // Output
    output reg [4:0] destReg  // Output register value (selected based on the control signal)
);

always @(*)
begin
    if (regrt == 0)
        destReg = rd;    // If regrt is 0, select rd as the output.
    else
        destReg = rt;    // If regrt is 1, select rt as the output.
end

endmodule

module RegisterFile(
    // Inputs
    input [4:0] rs,     // Input for the source register (rs)
    input [4:0] rt,     // Input for the target register (rt)
    
    //Lab 5 Inputs
    input [4:0] wdestReg,
    input [31:0] wbData,
    input wwreg,
    input clk,

    // Outputs
    output reg [31:0] qa,  // Output for the value stored in the source register
    output reg [31:0] qb   // Output for the value stored in the target register
    
);

reg [31:0] register [0:31]; // 32x32 array for registers (register file)

// Initialize all registers to 0
integer r;
initial begin
    for (r = 11; r <= 31; r = r + 1) begin
        register[r] = 0;  // Initialize each register to 0.
        
    register[0] = 32'h00000000;
    register[1] = 32'hA00000AA;
    register[2] = 32'h10000011;
    register[3] = 32'h20000022;
    register[4] = 32'h30000033;
    register[5] = 32'h40000044;
    register[6] = 32'h50000055;
    register[7] = 32'h60000066;
    register[8] = 32'h70000077;
    register[9] = 32'h80000088;
    register[10] = 32'h90000099;
    
    end
end

always @ (*) // Always block to update qa and qb based on the input rs and rt values.
begin
    qa = register[rs];  // Output qa is the value stored in the source register (rs).
    qb = register[rt];  // Output qb is the value stored in the target register (rt).
end

always @ (negedge clk)
    begin
        if (wwreg == 1)
            register[wdestReg] = wbData;
    end

endmodule

module ImmediateExtender( //immediate extender module.
    input [15:0] imm,
    output reg [31:0] imm32
    );
    
    always @ (*) //always block to update the value of imm32.
        begin
            imm32 = {{16{imm[15]}}, imm}; //sets imm32 to be equal to imm. the last bit is concatinated to the other 16 bits based on if the sign bit is a zero or one.
        end
endmodule

module IDEXEpipeline(
    // Inputs
    input wreg,           // Control signal for writing to the register file
    input m2reg,          // Control signal for writing to the register file (M2 stage)
    input wmem,           // Control signal for writing to memory
    input [3:0] aluc,     // ALU control signal
    input aluimm,         // ALU immediate value
    input [4:0] destReg,  // Destination register address
    input [31:0] fwdAout,      // Value from source register A
    input [31:0] fwdBout,      // Value from source register B
    input [31:0] imm32,   // 32-bit immediate value
    input clk,            // Clock signal

    // Outputs
    output reg ewreg,     // Output for write enable signal
    output reg em2reg,    // Output for write enable signal (M2 stage)
    output reg ewmem,     // Output for memory write enable signal
    output reg [3:0] ealuc,   // Output for ALU control signal
    output reg ealuimm,   // Output for ALU immediate value
    output reg [4:0] edestReg,   // Output for destination register address
    output reg [31:0] eqa,  // Output for source register A value
    output reg [31:0] eqb,  // Output for source register B value
    output reg [31:0] eimm32 // Output for 32-bit immediate value
);

// On the positive edge of the clock, update the output signals with the input values.
always @ (posedge clk)
begin
    ewreg = wreg;
    em2reg = m2reg;
    ewmem = wmem;
    ealuc = aluc;
    ealuimm = aluimm;
    edestReg = destReg;
    eqa = fwdAout;
    eqb = fwdBout;
    eimm32 = imm32;
end

endmodule

module ALU(
    input [31:0] eqa,     // Input A for the ALU
    input [31:0] b,       // Input B for the ALU
    input [3:0] ealuc,    // ALU control signal
    output reg [31:0] r   // Output of the ALU
);


always @ (*) 
begin
    case(ealuc)
        4'b0000: r = eqa & b; // AND operation
        4'b0001: r = eqa | b; // OR operation
        4'b0010: r = eqa + b; // ADD operation
        4'b0110: r = eqa - b; // SUBTRACT operation
        4'b1100: r = ~(eqa | b); // NOR operation
        4'b0011: r = eqa ^ b; // XOR operation
    endcase
end
endmodule

module ALUMux(
    input [31:0] eqb,    // Input B data from the ALU
    input [31:0] eimm32, // Immediate value from the pipeline
    input ealuimm,        // Mux control signal
    output reg [31:0] b  // Output data selected by the Mux
);

always @(*) begin
    case(ealuimm)
        1'b0: // Select eqb as the output
            begin
                b <= eqb; 
            end
        1'b1: // Select eimm32 as the output
            begin
                b <= eimm32;
            end
    endcase
end

endmodule

module EXEMEMpipeline(
    input ewreg,            // Control signal for writing to the register file
    input em2reg,           // Control signal for writing to the register file (Memory stage)
    input ewmem,            // Control signal for writing to memory
    input [4:0] edestReg,   // Destination register address
    input [31:0] r,         // Result from the ALU
    input [31:0] eqb,       // Value from source register B
    input clk,              // Clock signal

    output reg mwreg,       // Output for write enable signal
    output reg mm2reg,      // Output for write enable signal (M2 stage)
    output reg mwmem,       // Output for memory write enable signal
    output reg [4:0] mdestReg, // Output for destination register address
    output reg [31:0] mr,    // Output for result from the ALU
    output reg [31:0] mqb    // Output for value from source register B
);

always @ (posedge clk)
begin
    mwreg = ewreg;
    mm2reg = em2reg;
    mwmem = ewmem;
    mdestReg = edestReg;
    mr = r;
    mqb = eqb;
end

endmodule

module DataMemory(
    input [31:0] mr,     // Memory read address
    input [31:0] mqb,    // Data to be written to memory
    input mwmem,         // Memory write control signal
    input clk,           // Clock signal
    output reg [31:0] mdo // Data read from memory
);

// Define a data memory array with 64 words
reg [31:0] dataMemory [0:63];

// Initialize data memory with some values (words 0-9)
initial begin
    dataMemory[0] = 32'hA00000AA;
    dataMemory[1] = 32'h10000011;
    dataMemory[2] = 32'h20000022;
    dataMemory[3] = 32'h30000033;
    dataMemory[4] = 32'h40000044;
    dataMemory[5] = 32'h50000055;
    dataMemory[6] = 32'h60000066;
    dataMemory[7] = 32'h70000077;
    dataMemory[8] = 32'h80000088;
    dataMemory[9] = 32'h90000099;
end

always @(*) begin
    // Reading: Set mdo to the value at the memory read address (bits 7:2 of mr)
    mdo = dataMemory[mr[7:2]];
end

always @(negedge clk) begin
    // Writing: If mwmem is 1, write the value in mqb to the memory at the read address
    if (mwmem == 1) begin
        //dataMemory[mr[7:2]] <= mqb;
        dataMemory[mr] <= mqb;
    end
end

endmodule

module MEMWBpipeline(
    input mwreg,              
    input mm2reg,             
    input [4:0] mdestReg,     
    input [31:0] mr,          
    input [31:0] mdo,        
    input clk,               

    output reg wwreg,         // Output for write enable signal
    output reg wm2reg,        // Output for write enable signal (Memory stage)
    output reg [4:0] wdestReg, // Output for destination register address
    output reg [31:0] wr,    // Output for result from the data memory
    output reg [31:0] wdo    // Output for data read from the data memory
);

always @ (posedge clk)
begin
    wwreg = mwreg;
    wm2reg = mm2reg;
    wdestReg = mdestReg;
    wr = mr;
    wdo = mdo;
end

endmodule

module WbMux(
    input [31:0] wr,
    input [31:0] wdo,
    input wm2reg,
    output reg [31:0] wbData
    );
    
    always @ (*)
        begin
            if (wm2reg == 0)
                wbData = wr;
            else
                wbData = wdo;
        end
endmodule

module Fwd_FwdMuxA(
    input [1:0] fwda,
    input [31:0] qa,
    input [31:0] r,
    input [31:0] mr,
    input [31:0] mdo,
    output reg [31:0] fwdAout
    );
    
    always @ (*) begin
        case(fwda)
                2'b00: fwdAout <= qa;
                2'b01: fwdAout <= r;
                2'b10: fwdAout <= mr;
                2'b11: fwdAout <= mdo;
         endcase
    end
endmodule

module Fwd_FwdMuxB(
    input [1:0] fwdb,
    input [31:0] qb,
    input [31:0] r,
    input [31:0] mr,
    input [31:0] mdo,
    output reg [31:0] fwdBout
    );
    
    always @ (*) begin
        case(fwdb)
                2'b00: fwdBout <= qb;
                2'b01: fwdBout <= r;
                2'b10: fwdBout <= mr;
                2'b11: fwdBout <= mdo;
         endcase
    end
    
endmodule



module Datapath(
   
    input clk,               // Clock signal
    output wire [31:0] pc,   // Program Counter
    output wire [31:0] dinstOut // Data from the Instruction Memory

);
   
    wire wreg;               // Control signal for write enable
    wire m2reg;              // Control signal for write enable (Memory stage)
    wire wmem;               // Control signal for memory write enable
    wire aluimm;             // ALU immediate value
    wire regrt;              // Control signal for selecting a register
    wire [4:0] destReg;      // Destination register address
    wire [31:0] qa;          // Data from source register A
    wire [31:0] qb;          // Data from source register B
    wire [31:0] imm32;      // 32-bit immediate value
    wire [31:0] nextPc;     // Next program counter value
    wire [31:0] instOut;    // Data from the Instruction Memory
    wire [3:0] aluc;        // ALU control signal
    wire [15:0] imm;        // Immediate value
    wire [4:0] rs;          // Source register address
    wire [4:0] rt;          // Source register address
    wire [4:0] rd;          // Destination register address
    wire [5:0] op;          // Operation code
    wire [5:0] func;        // Function code

    wire [31:0] b;          // Data input to the ALU
    wire [31:0] r;          // Result from the ALU
    wire [31:0] mdo;       // Data read from memory or result from ALU
   
    wire [31:0]wbData;
    
    wire wpcir;
    wire [1:0] fwda;
    wire [1:0] fwdb;
    wire [31:0] fwdAout;
    wire [31:0] fwdBout;
    
     wire ewreg;        // Control signal for write enable in the EX stage
     wire em2reg;      // Control signal for write enable in the Memory stage
     wire ewmem;       // Control signal for write enable in the MEM stage
     wire [3:0] ealuc;  // ALU control signal in the EX stage
     wire ealuimm;     // ALU immediate in the EX stage
     wire [4:0] edestReg; // Destination register address in the EX stage
     wire [31:0] eqa;   // Data from source register A in the EX stage
     wire [31:0] eqb;   // Data from source register B in the EX stage
     wire [31:0] eimm32; // 32-bit immediate in the EX stage
   
     wire mwreg;        
     wire mm2reg;       
     wire mwmem;       
     wire [4:0] mdestReg; 
     wire [31:0] mr;    
     wire [31:0] mqb;   
    
     wire wwreg;       
     wire wm2reg;       
     wire [4:0] wdestReg; 
     wire [31:0] wr;    
     wire [31:0] wdo;   
    
    ProgramCounter IF_ProgramCounter_dp(.clk(clk), .nextPc(nextPc), .wpcir(wpcir), .pc(pc));
    pcAdder IF_pcAdder_dp(.pc(pc), .nextPc(nextPc));
    InstructionMemory IF_InstructionMemory_dp(.pc(pc), .instOut(instOut));
    IFIDpipelineReg IFIDpipelineReg_dp(.clk(clk), .instOut(instOut), .wpcir(wpcir), .dinstOut(dinstOut));
    ControlUnit ID_controlUnit_dp(
    .op(op),
    .func(func),
    .rs(rs),
    .rt(rt),
    .mdestReg(mdestReg),
    .mm2reg(mm2reg),
    .mwreg(mwreg),
    .edestReg(edestReg),
    .em2reg(em2reg),
    .ewreg(ewreg),
    .wreg(wreg), 
    .m2reg(m2reg), 
    .wmem(wmem), 
    .aluc(aluc), 
    .aluimm(aluimm), 
    .regrt(regrt),
    .fwda(fwda),
    .fwdb(fwdb),
    .wpcir(wpcir)
    );
    
    RegrtMultiplexer ID_RegrtMultiplexer_dp(.rt(rt), .rd(rd), .regrt(regrt), .destReg(destReg));
    RegisterFile ID_RegisterFile_dp(.rs(rs), .rt(rt), .wdestReg(wdestReg), .wbData(wbData), .wwreg(wwreg), .clk(clk), .qa(qa), .qb(qb));
    ImmediateExtender ID_ImmediateExtender_dp(.imm(imm), .imm32(imm32));
    IDEXEpipeline IDEXEpipeline_dp(
        .wreg(wreg), 
        .m2reg(m2reg), 
        .wmem(wmem), 
        .aluc(aluc), 
        .aluimm(aluimm), 
        .destReg(destReg), 
        .fwdAout(fwdAout), 
        .fwdBout(fwdBout), 
        .imm32(imm32), 
        .clk(clk), 
        .ewreg(ewreg), 
        .em2reg(em2reg), 
        .ewmem(ewmem), 
        .ealuc(ealuc), 
        .ealuimm(ealuimm), 
        .edestReg(edestReg), 
        .eqa(eqa), 
        .eqb(eqb), 
        .eimm32(eimm32)
    );
    
    ALU EXE_ALU_dp(.eqa(eqa), .b(b), .ealuc(ealuc), .r(r));
    ALUMux EXE_ALUMux_dp(.eqb(eqb), .eimm32(eimm32), .ealuimm(ealuimm), .b(b));
    EXEMEMpipeline EXEMempipeline_dp(
        .ewreg(ewreg),
        .em2reg(em2reg),
        .ewmem(ewmem),
        .edestReg(edestReg),
        .r(r), 
        .eqb(eqb),
        .clk(clk),
        .mwreg(mwreg),
        .mm2reg(mm2reg),
        .mwmem(mwmem),
        .mdestReg(mdestReg),
        .mr(mr),
        .mqb(mqb)
    );
    DataMemory MEM_DataMemory_dp(.mr(mr), .mqb(mqb), .mwmem(mwmem), .clk(clk), .mdo(mdo));
       
    MEMWBpipeline MEMWBpipeline_dp(
        .mwreg(mwreg),
        .mm2reg(mm2reg),
        .mdestReg(mdestReg),
        .mr(mr),
        .mdo(mdo),
        .clk(clk),
        .wwreg(wwreg),
        .wm2reg(wm2reg),
        .wdestReg(wdestReg),
        .wr(wr),
        .wdo(wdo)
    );
    
    WbMux WB_WbMux_dp(.wr(wr), .wdo(wdo), .wm2reg(wm2reg), .wbData(wbData));
    
    Fwd_FwdMuxA Fwd_FwdMuxA_dp(.fwda(fwda), .qa(qa), .r(r), .mr(mr), .mdo(mdo), .fwdAout(fwdAout));
    Fwd_FwdMuxB Fwd_FwdMuxB_dp(.fwdb(fwdb), .qb(qb), .r(r), .mr(mr), .mdo(mdo), .fwdBout(fwdBout));

    assign op = dinstOut[31:26];
    assign func = dinstOut[5:0];
    assign rs = dinstOut[25:21];
    assign rt = dinstOut[20:16];
    assign rd = dinstOut[15:11];
    assign imm = dinstOut[15:0];
endmodule
