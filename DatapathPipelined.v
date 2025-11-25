`timescale 1ns / 1ns

// registers are 32 bits in RV32
`define REG_SIZE 31

// inst. are 32 bits in RV32IM
`define INST_SIZE 31

// RV opcodes are 7 bits
`define OPCODE_SIZE 6

`define DIVIDER_STAGES 8

// Don't forget your old codes
//`include "cla.v"
//`include "DividerUnsignedPipelined.v"

module RegFile (
  input      [        4:0] rd,
  input      [`REG_SIZE:0] rd_data,
  input      [        4:0] rs1,
  output reg [`REG_SIZE:0] rs1_data,
  input      [        4:0] rs2,
  output reg [`REG_SIZE:0] rs2_data,
  input                    clk,
  input                    we,
  input                    rst
);
  localparam NumRegs = 32;
  reg [`REG_SIZE:0] regs[0:NumRegs-1];

  // TODO: your code here

endmodule

module DatapathPipelined (
  input                     clk,
  input                     rst,
  output     [ `REG_SIZE:0] pc_to_imem,
  input      [`INST_SIZE:0] inst_from_imem,
  // dmem is read/write
  output reg [ `REG_SIZE:0] addr_to_dmem,
  input      [ `REG_SIZE:0] load_data_from_dmem,
  output reg [ `REG_SIZE:0] store_data_to_dmem,
  output reg [         3:0] store_we_to_dmem,
  output reg                halt,
  // The PC of the inst currently in Writeback. 0 if not a valid inst.
  output reg [ `REG_SIZE:0] trace_writeback_pc,
  // The bits of the inst currently in Writeback. 0 if not a valid inst.
  output reg [`INST_SIZE:0] trace_writeback_inst
);

  // opcodes - see section 19 of RiscV spec
  localparam [`OPCODE_SIZE:0] OpcodeLoad    = 7'b00_000_11;
  localparam [`OPCODE_SIZE:0] OpcodeStore   = 7'b01_000_11;
  localparam [`OPCODE_SIZE:0] OpcodeBranch  = 7'b11_000_11;
  localparam [`OPCODE_SIZE:0] OpcodeJalr    = 7'b11_001_11;
  localparam [`OPCODE_SIZE:0] OpcodeMiscMem = 7'b00_011_11;
  localparam [`OPCODE_SIZE:0] OpcodeJal     = 7'b11_011_11;

  localparam [`OPCODE_SIZE:0] OpcodeRegImm  = 7'b00_100_11;
  localparam [`OPCODE_SIZE:0] OpcodeRegReg  = 7'b01_100_11;
  localparam [`OPCODE_SIZE:0] OpcodeEnviron = 7'b11_100_11;

  localparam [`OPCODE_SIZE:0] OpcodeAuipc   = 7'b00_101_11;
  localparam [`OPCODE_SIZE:0] OpcodeLui     = 7'b01_101_11;

  // cycle counter, not really part of any stage but useful for orienting within GtkWave
  // do not rename this as the testbench uses this value
  reg [`REG_SIZE:0] cycles_current;
  always @(posedge clk) begin
    if (rst) begin
      cycles_current <= 0;
    end else begin
      cycles_current <= cycles_current + 1;
    end
  end

  // ALU OP
      localparam ALU_ADD  = 4'b0000;
      localparam ALU_SUB  = 4'b0001;
      localparam ALU_AND  = 4'b0010;
      localparam ALU_OR   = 4'b0011;
      localparam ALU_XOR  = 4'b0100;
      localparam ALU_SLT  = 4'b0101; 
      localparam ALU_SLTU = 4'b0110; 
      localparam ALU_SLL  = 4'b0111;
      localparam ALU_SRL  = 4'b1000;
      localparam ALU_SRA  = 4'b1001;
    
    // Funct3 Codes
    // Arithmetic / Logic
      localparam F3_ADD_SUB = 3'b000; // ADD/SUB/ADDI
      localparam F3_SLL     = 3'b001;
      localparam F3_SLT     = 3'b010;
      localparam F3_SLTU    = 3'b011;
      localparam F3_XOR     = 3'b100;
      localparam F3_SRL_SRA = 3'b101;
      localparam F3_OR      = 3'b110;
      localparam F3_AND     = 3'b111;
      
      // Branch
      localparam F3_BEQ     = 3'b000;
      localparam F3_BNE     = 3'b001;
      localparam F3_BLT     = 3'b100;
      localparam F3_BGE     = 3'b101;
      localparam F3_BLTU    = 3'b110;
      localparam F3_BGEU    = 3'b111;
    
      // Load/Store
      localparam F3_B       = 3'b000; // Byte
      localparam F3_H       = 3'b001; // Half
      localparam F3_W       = 3'b010; // Word
    
      // 4. Funct7 Codes
      localparam F7_NORMAL  = 7'b0000000;
      localparam F7_SUB_SRA = 7'b0100000;
   
  // Pipeline regs
  // IF/ID
    reg [`REG_SIZE:0] d_pc;
    reg [`INST_SIZE:0] d_inst;
  
  // ID/EX Registers
    reg [`REG_SIZE:0] x_pc;
    reg [`REG_SIZE:0] x_rs1_data, x_rs2_data;
    reg [`REG_SIZE:0] x_imm;
    reg [4:0] x_rs1_addr, x_rs2_addr, x_rd_addr;
    reg [3:0] x_alu_op;
    reg x_reg_we, x_mem_we, x_branch, x_jump, x_jal, x_jalr, x_load, x_auipc, x_lui;
    reg [1:0] x_op1_sel, x_op2_sel;
    reg [3:0] x_mem_mask;
    reg [`INST_SIZE:0] x_inst; 
    
  // EX/MEM Registers
    reg [`REG_SIZE:0] m_pc;
    reg [`REG_SIZE:0] m_alu_result;
    reg [`REG_SIZE:0] m_store_data;
    reg [4:0] m_rd_addr;
    reg m_reg_we, m_mem_we, m_load;
    reg [3:0] m_mem_mask;
    reg [`INST_SIZE:0] m_inst;

  // MEM/WB Registers
    reg [`REG_SIZE:0] w_pc;
    reg [`REG_SIZE:0] w_alu_result;
    reg [`REG_SIZE:0] w_mem_data;
    reg [4:0] w_rd_addr;
    reg w_reg_we, w_load;
    reg [`INST_SIZE:0] w_inst;  
    
  /***************/
  /* FETCH STAGE */
  /***************/

    reg  [`REG_SIZE:0] f_pc_current;
    wire [`REG_SIZE:0] f_pc_next;
    wire [`REG_SIZE:0] f_inst;

    wire branch_taken; 
    wire [`REG_SIZE:0] branch_target;
    
    assign f_pc_next = (branch_taken) ? branch_target : (f_pc_current + 4);
    assign pc_to_imem = f_pc_current;

  // program counter
    always @(posedge clk) begin
      if (rst) begin
        f_pc_current <= 32'd0;
      end else begin
        f_pc_current <= f_pc_next;
      end
    end
    // send PC to imem
    assign pc_to_imem = f_pc_current;
    assign f_inst = inst_from_imem;

    always @(posedge clk) begin
        if (rst || branch_taken) begin
            d_pc <= 0;
            d_inst <= 0; // NOP
        end else begin
            d_pc <= f_pc_current;
            d_inst <= inst_from_imem;
        end
    end

  /****************/
  /* DECODE STAGE */
  /****************/
    wire [6:0] opcode = d_inst[6:0];
    wire [4:0] rd     = d_inst[11:7];
    wire [2:0] funct3 = d_inst[14:12];
    wire [4:0] rs1    = d_inst[19:15];
    wire [4:0] rs2    = d_inst[24:20];
    wire [6:0] funct7 = d_inst[31:25];

    wire [`REG_SIZE:0] imm_i = {{20{d_inst[31]}}, d_inst[31:20]}; 
    wire [`REG_SIZE:0] imm_s = {{20{d_inst[31]}}, funct7, rd};
    wire [`REG_SIZE:0] imm_b = {{19{d_inst[31]}}, d_inst[31], d_inst[7], d_inst[30:25], d_inst[11:8], 1'b0};
    wire [`REG_SIZE:0] imm_j = {{11{d_inst[31]}}, d_inst[31], d_inst[19:12], d_inst[20], d_inst[30:21], 1'b0};
    wire [`REG_SIZE:0] imm_u = {d_inst[31:12], 12'b0};

    wire [`REG_SIZE:0] rf_rs1_data_raw, rf_rs2_data_raw;
    reg  [`REG_SIZE:0] rf_rs1_data_fwd, rf_rs2_data_fwd;
    wire [`REG_SIZE:0] wb_data;
    
    // WD bypass
    always @(*) begin
        if (w_reg_we && (w_rd_addr != 0) && (w_rd_addr == rs1)) rf_rs1_data_fwd = wb_data;
        else rf_rs1_data_fwd = rf_rs1_data_raw;

        if (w_reg_we && (w_rd_addr != 0) && (w_rd_addr == rs2)) rf_rs2_data_fwd = wb_data;
        else rf_rs2_data_fwd = rf_rs2_data_raw;
    end

    // Control logic
    reg [4:0] ctrl_alu_op;
    reg ctrl_reg_we, ctrl_mem_we, ctrl_branch, ctrl_jal, ctrl_jalr, ctrl_load, ctrl_auipc, ctrl_lui;
    reg [3:0] ctrl_mem_mask;
    reg [1:0] ctrl_op1_sel; 
    reg [1:0] ctrl_op2_sel;

    always @(*) begin
        ctrl_alu_op = ALU_ADD; 
        ctrl_reg_we = 0; 
        ctrl_mem_we = 0; 
        ctrl_branch = 0;
        ctrl_jal = 0; 
        ctrl_jalr = 0; 
        ctrl_load = 0; 
        ctrl_auipc = 0; 
        ctrl_lui = 0;
        ctrl_mem_mask = 4'b0000; 
        ctrl_op1_sel = 0; 
        ctrl_op2_sel = 0;
        
        case (opcode) 
            OpcodeRegReg: begin
                ctrl_reg_we = 1;
                if (funct7 == F7_NORMAL) begin 
                    case(funct3)
                        F3_ADD_SUB: ctrl_alu_op = ALU_ADD;
                        F3_SLL:     ctrl_alu_op = ALU_SLL;
                        F3_SLT:     ctrl_alu_op = ALU_SLT;
                        F3_SLTU:    ctrl_alu_op = ALU_SLTU;
                        F3_XOR:     ctrl_alu_op = ALU_XOR;
                        F3_SRL_SRA: ctrl_alu_op = ALU_SRL;
                        F3_OR:      ctrl_alu_op = ALU_OR;
                        F3_AND:     ctrl_alu_op = ALU_AND;
                    endcase
                end 
                else if (funct7 == F7_SUB_SRA) begin 
                    case(funct3)
                        F3_ADD_SUB: ctrl_alu_op = ALU_SUB;
                        F3_SRL_SRA: ctrl_alu_op = ALU_SRA;
                    endcase
                end
            end
            
            OpcodeRegImm: begin
                ctrl_reg_we = 1; 
                ctrl_op2_sel = 1; // Imm
                case(funct3)
                    F3_ADD_SUB: ctrl_alu_op = ALU_ADD; 
                    F3_SLT:     ctrl_alu_op = ALU_SLT; 
                    F3_SLTU:    ctrl_alu_op = ALU_SLTU; 
                    F3_XOR:     ctrl_alu_op = ALU_XOR;
                    F3_OR:      ctrl_alu_op = ALU_OR;  
                    F3_AND:     ctrl_alu_op = ALU_AND; 
                    F3_SLL:     ctrl_alu_op = ALU_SLL; 
                    F3_SRL_SRA: ctrl_alu_op = (funct7[5]) ? ALU_SRA : ALU_SRL; // SRAI / SRLI
                endcase                
            end
            
            OpcodeLoad: begin
                ctrl_reg_we = 1; 
                ctrl_load = 1; //imm
                ctrl_op2_sel = 1; 
                ctrl_alu_op = ALU_ADD;
            end
            
            OpcodeStore: begin
                ctrl_mem_we = 1; 
                ctrl_op2_sel = 2; // imm_s
                ctrl_alu_op = ALU_ADD;
                if (funct3 == F3_B) ctrl_mem_mask = 4'b0001;
                else if (funct3 == F3_H) ctrl_mem_mask = 4'b0011;
                else ctrl_mem_mask = 4'b1111; // Word
            end
            
            OpcodeBranch: begin
                ctrl_branch = 1; 
                ctrl_alu_op = ALU_ADD;
            end
            
            OpcodeJal: begin
                ctrl_jal = 1; 
                ctrl_reg_we = 1;
            end
            
            OpcodeJalr: begin
                ctrl_jalr = 1;
                ctrl_reg_we = 1;
                ctrl_op2_sel = 1;
            end
                        
            OpcodeLui: begin
                ctrl_lui = 1; 
                ctrl_reg_we = 1;
            end 
            
            OpcodeAuipc: begin
                ctrl_auipc = 1;
                ctrl_reg_we = 1;
            end
            
            OpcodeEnviron: begin
                if (funct3 == 0) halt = 1;
            end        
        endcase
    end

    reg [`REG_SIZE:0] decoded_imm;
    always @(*) begin
        case(opcode)
            OpcodeStore: decoded_imm = imm_s;
            OpcodeBranch: decoded_imm = imm_b;
            OpcodeJal: decoded_imm = imm_j;
            OpcodeLui, OpcodeAuipc: decoded_imm = imm_u;
            default: decoded_imm = imm_i; 
        endcase
    end
    
    always @(posedge clk) begin
        if (rst || branch_taken) begin 
            x_reg_we <= 0; 
            x_mem_we <= 0; 
            x_branch <= 0; 
            x_jal <= 0; 
            x_jalr <= 0;
            x_inst <= 0; 
        end else begin
            x_pc <= d_pc;
            x_rs1_data <= rf_rs1_data_fwd;
            x_rs2_data <= rf_rs2_data_fwd;
            x_imm <= decoded_imm;
            x_rs1_addr <= rs1;
            x_rs2_addr <= rs2;
            x_rd_addr <= rd;
            x_alu_op <= ctrl_alu_op;
            x_reg_we <= ctrl_reg_we;
            x_mem_we <= ctrl_mem_we;
            x_branch <= ctrl_branch;
            x_jal <= ctrl_jal;
            x_jalr <= ctrl_jalr;
            x_load <= ctrl_load;
            x_auipc <= ctrl_auipc;
            x_lui <= ctrl_lui;
            x_op1_sel <= ctrl_op1_sel;
            x_op2_sel <= ctrl_op2_sel;
            x_mem_mask <= ctrl_mem_mask;
            x_inst <= d_inst;
        end
    end

    RegFile rf (
        .clk(clk), 
        .rst(rst), 
        .we(w_reg_we), 
        .rd(w_rd_addr), 
        .rd_data(wb_data),
        .rs1(rs1), 
        .rs2(rs2), 
        .rs1_data(rf_rs1_data_raw), 
        .rs2_data(rf_rs2_data_raw)
    );

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`

endmodule

module MemorySingleCycle #(
    parameter NUM_WORDS = 512
) (
    input                    rst,                 // rst for both imem and dmem
    input                    clk,                 // clock for both imem and dmem
	                                              // The memory reads/writes on @(negedge clk)
    input      [`REG_SIZE:0] pc_to_imem,          // must always be aligned to a 4B boundary
    output reg [`REG_SIZE:0] inst_from_imem,      // the value at memory location pc_to_imem
    input      [`REG_SIZE:0] addr_to_dmem,        // must always be aligned to a 4B boundary
    output     [`REG_SIZE:0] load_data_from_dmem, // the value at memory location addr_to_dmem
    input      [`REG_SIZE:0] store_data_to_dmem,  // the value to be written to addr_to_dmem, controlled by store_we_to_dmem
    // Each bit determines whether to write the corresponding byte of store_data_to_dmem to memory location addr_to_dmem.
    // E.g., 4'b1111 will write 4 bytes. 4'b0001 will write only the least-significant byte.
    input      [        3:0] store_we_to_dmem
);

  // memory is arranged as an array of 4B words
  reg [`REG_SIZE:0] mem_array[0:NUM_WORDS-1];

  // preload instructions to mem_array
  initial begin
    $readmemh("mem_initial_contents.hex", mem_array);
  end

    assign load_data_from_dmem = mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}];

  localparam AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam AddrLsb = 2;

  always @(negedge clk) begin
    inst_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
  end

  always @(negedge clk) begin
    if (store_we_to_dmem[0]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][7:0] <= store_data_to_dmem[7:0];
    end
    if (store_we_to_dmem[1]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][15:8] <= store_data_to_dmem[15:8];
    end
    if (store_we_to_dmem[2]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][23:16] <= store_data_to_dmem[23:16];
    end
    if (store_we_to_dmem[3]) begin
      mem_array[addr_to_dmem[AddrMsb:AddrLsb]][31:24] <= store_data_to_dmem[31:24];
    end
    // dmem is "read-first": read returns value before the write
  end
endmodule

/* This design has just one clock for both processor and memory. */
module Processor (
    input                 clk,
    input                 rst,
    output                halt,
    output [ `REG_SIZE:0] trace_writeback_pc,
    output [`INST_SIZE:0] trace_writeback_inst
);

  wire [`INST_SIZE:0] inst_from_imem;
  wire [ `REG_SIZE:0] pc_to_imem, mem_data_addr, mem_data_loaded_value, mem_data_to_write;
  wire [         3:0] mem_data_we;

  // This wire is set by cocotb to the name of the currently-running test, to make it easier
  // to see what is going on in the waveforms.
  wire [(8*32)-1:0] test_case;

  MemorySingleCycle #(
      .NUM_WORDS(8192)
  ) memory (
    .rst                 (rst),
    .clk                 (clk),
    // imem is read-only
    .pc_to_imem          (pc_to_imem),
    .inst_from_imem      (inst_from_imem),
    // dmem is read-write
    .addr_to_dmem        (mem_data_addr),
    .load_data_from_dmem (mem_data_loaded_value),
    .store_data_to_dmem  (mem_data_to_write),
    .store_we_to_dmem    (mem_data_we)
  );

  DatapathPipelined datapath (
    .clk                  (clk),
    .rst                  (rst),
    .pc_to_imem           (pc_to_imem),
    .inst_from_imem       (inst_from_imem),
    .addr_to_dmem         (mem_data_addr),
    .store_data_to_dmem   (mem_data_to_write),
    .store_we_to_dmem     (mem_data_we),
    .load_data_from_dmem  (mem_data_loaded_value),
    .halt                 (halt),
    .trace_writeback_pc   (trace_writeback_pc),
    .trace_writeback_inst (trace_writeback_inst)
  );

endmodule
