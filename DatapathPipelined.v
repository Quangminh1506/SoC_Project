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
  integer i;

  // TODO: your code here
  always @(posedge clk) begin
    if (rst) begin
      for (i = 0; i < NumRegs; i = i + 1) begin
        regs[i] <= 0;
      end
    end else begin
      if (we && (rd != 0)) begin
        regs[rd] <= rd_data;
      end
    end
  end

  always @(*) begin
    rs1_data = (rs1 == 5'd0) ? 0 : regs[rs1];
    rs2_data = (rs2 == 5'd0) ? 0 : regs[rs2];
  end
  
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
      localparam ALU_MUL  = 4'b1010;
      localparam ALU_MULH = 4'b1011;
      localparam ALU_MULHSU = 4'b1100;
      localparam ALU_MULHU = 4'b1101;
    
    
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
      
      // Extend multiply
      localparam F3_MUL     = 3'b000;
      localparam F3_MULH    = 3'b001;
      localparam F3_MULHSU  = 3'b010;
      localparam F3_MULHU   = 3'b011;
      
      //Extend divide
      localparam F3_DIV     = 3'b100;
      localparam F3_DIVU    = 3'b101;
      localparam F3_REM     = 3'b110;
      localparam F3_REMU    = 3'b111;
    
      // Load/Store
      localparam F3_B       = 3'b000; // Byte
      localparam F3_H       = 3'b001; // Half
      localparam F3_W       = 3'b010; // Word
    
      // 4. Funct7 Codes
      localparam F7_NORMAL  = 7'b0000000;
      localparam F7_SUB_SRA = 7'b0100000;
      localparam F7_M_EXT   = 7'b0000001;
      
  // Pipeline regs
  // IF/ID
    reg [`REG_SIZE:0] d_pc, d_inst;
  
  // ID/EX Registers
    reg [`REG_SIZE:0] x_pc;
    reg [`REG_SIZE:0] x_rs1_data, x_rs2_data;
    reg [`REG_SIZE:0] x_imm;
    reg [4:0] x_rs1_addr, x_rs2_addr, x_rd_addr;
    reg [3:0] x_alu_op;
    reg x_reg_we, x_mem_we, x_branch, x_jump, x_jal, x_jalr, x_load, x_auipc, x_lui;
    reg x_is_div_op, x_div_signed, x_div_get_rem; 
    reg [2:0] x_funct3; 
    reg [1:0] x_op1_sel, x_op2_sel;
    reg [3:0] x_mem_mask;
    reg [`INST_SIZE:0] x_inst; 
    
  // EX/MEM Registers
    reg [`REG_SIZE:0] m_pc;
    reg [`REG_SIZE:0] m_alu_result;
    reg [`REG_SIZE:0] m_store_data;
    reg [4:0] m_rd_addr, m_rs2_addr;
    reg m_reg_we, m_mem_we, m_load;
    reg [2:0] m_funct3;
    
    reg [3:0] m_mem_mask;
    reg [`INST_SIZE:0] m_inst;

  // MEM/WB Registers
    reg [`REG_SIZE:0] w_pc, w_alu_result, w_mem_data;
    reg [4:0] w_rd_addr;
    reg w_reg_we, w_load;
    reg [2:0] w_funct3;
    reg [1:0] w_byte_offset;
    reg [`INST_SIZE:0] w_inst;
      
    // check divider
    reg [6:0] div_busy [0:7];
    
  // Stall (Hazard control) signal
  wire stall_pipeline; // stall all (hazard)      
  wire stall_load_use; // stall load      
  wire stall_div_dependency; //stall depend
    
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
    
    // Hazard detection
    // Divider denpendency
    integer i;
    reg conflict_div;
    
    always @(*) begin
        conflict_div = 0;
        for (i = 0; i < 8; i = i + 1) begin
            if (div_busy[i][6] && div_busy[i][4:0] != 0 && (div_busy[i][4:0] == rs1 || div_busy[i][4:0] == rs2)) 
              conflict_div = 1;
        end    
    end
    
    assign stall_div_dependency = conflict_div;
    
    // Load hazard
    assign stall_load_use = (x_load && (x_rd_addr != 0) && 
                            (x_rd_addr == rs1 || x_rd_addr == rs2));
    
    //Stall all
    assign stall_pipeline = stall_div_dependency || stall_load_use;

    // Control logic
    reg [4:0] ctrl_alu_op;
    reg ctrl_reg_we, ctrl_mem_we, ctrl_branch, ctrl_jal, ctrl_jalr, ctrl_load, ctrl_auipc, ctrl_lui;
    reg ctrl_is_div_op, ctrl_div_signed, ctrl_div_get_rem;
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
        ctrl_op1_sel = 0; 
        ctrl_op2_sel = 0;
        
        case (opcode) 
            OpcodeRegReg: begin
                ctrl_reg_we = 1;
                if (funct7 == F7_M_EXT) begin
                    case (funct3)
                        F3_MUL:    ctrl_alu_op = ALU_MUL;
                        F3_MULH:   ctrl_alu_op = ALU_MULH;
                        F3_MULHSU: ctrl_alu_op = ALU_MULHSU;
                        F3_MULHU:  ctrl_alu_op = ALU_MULHU;
                        F3_DIV:  begin 
                            ctrl_is_div_op=1; 
                            ctrl_div_signed=1; 
                            ctrl_div_get_rem=0; 
                        end
                        F3_DIVU: begin 
                            ctrl_is_div_op=1; 
                            ctrl_div_signed=0; 
                            ctrl_div_get_rem=0; 
                        end
                        F3_REM:  begin ctrl_is_div_op=1; ctrl_div_signed=1; ctrl_div_get_rem=1; end
                        F3_REMU: begin ctrl_is_div_op=1; ctrl_div_signed=0; ctrl_div_get_rem=1; end
                    endcase
                end
                else if (funct7 == F7_NORMAL) begin 
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
                else begin  
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
//                if (funct3 == F3_B) ctrl_mem_mask = 4'b0001;
//                else if (funct3 == F3_H) ctrl_mem_mask = 4'b0011;
//                else ctrl_mem_mask = 4'b1111; // Word
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
        if (rst || branch_taken || stall_pipeline) begin 
            x_reg_we <= 0; 
            x_mem_we <= 0; 
            x_branch <= 0; 
            x_is_div_op <= 0;
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
            x_is_div_op <= ctrl_is_div_op;
            x_div_signed <= ctrl_div_signed;
            x_div_get_rem <= ctrl_div_get_rem;
            x_op1_sel <= ctrl_op1_sel;
            x_op2_sel <= ctrl_op2_sel;
            x_funct3 <= funct3;
//            x_mem_mask <= ctrl_mem_mask;
            x_inst <= d_inst;
        end
    end

    wire final_rf_we;
    reg [4:0] final_rf_dst;
    reg [`REG_SIZE:0] final_rf_data;
    
    RegFile rf (
        .clk(clk), 
        .rst(rst), 
        .we(final_rf_we), 
        .rd(final_rf_dst), 
        .rd_data(final_rf_data),
        .rs1(rs1), 
        .rs2(rs2), 
        .rs1_data(rf_rs1_data_raw), 
        .rs2_data(rf_rs2_data_raw)
    );

  // TODO: your code here, though you will also need to modify some of the code above
  // TODO: the testbench requires that your register file instance is named `rf`

  /****************/
  /* EXECUTE STAGE */
  /****************/
    
    reg [`REG_SIZE:0] alu_op1_fwd, alu_op2_fwd;
    always @(*) begin
        if (m_reg_we && m_rd_addr != 0 && m_rd_addr == x_rs1_addr) alu_op1_fwd = m_alu_result; 
        
        else if (w_reg_we && w_rd_addr != 0 && w_rd_addr == x_rs1_addr) alu_op1_fwd = wb_data;      

        else alu_op1_fwd = x_rs1_data;

        if (m_reg_we && m_rd_addr != 0 && m_rd_addr == x_rs2_addr) alu_op2_fwd = m_alu_result; 
        
        else if (w_reg_we && w_rd_addr != 0 && w_rd_addr == x_rs2_addr) alu_op2_fwd = wb_data; 
             
        else alu_op2_fwd = x_rs2_data;
    end

    wire [`REG_SIZE:0] alu_in1 = (x_auipc) ? x_pc : ((x_lui) ? 0 : alu_op1_fwd);
    wire [`REG_SIZE:0] alu_in2 = (x_jal || x_auipc || x_lui || x_op2_sel == 1 || x_op2_sel == 2) ? x_imm : alu_op2_fwd;

    wire [`REG_SIZE:0] alu_result;
    ALU alu_inst (
        .A(alu_in1), 
        .B(alu_in2), 
        .ALUOp(x_alu_op), 
        .result(alu_result), 
        .Zero()
    );
    
    // Divider
    wire [31:0] div_quotient, div_remainder;
    DividerPipelined div_inst (
        .clk(clk), 
        .rst(rst), 
        .stall(1'b0), 
        .is_signed(x_div_signed),
        .i_dividend(alu_op1_fwd), .i_divisor(alu_op2_fwd),
        .o_remainder(div_remainder), .o_quotient(div_quotient)
    );
  
    integer j;
    always @(posedge clk) begin
        if (rst) begin
            for(j = 0; j < 8; j = j + 1) div_busy[j] <= 0;
        end
        else begin
            for(j=1; j<8; j=j+1) begin
                div_busy[j] <= div_busy[j-1];
            end
            div_busy[0] <= {x_is_div_op, x_div_get_rem, x_rd_addr};
        end
    end

    //Branching logic
    wire branch_cond = (x_branch && (
      (x_funct3 == F3_BEQ  && alu_op1_fwd == alu_op2_fwd) || 
      (x_funct3 == F3_BNE  && alu_op1_fwd != alu_op2_fwd) || 
      (x_funct3 == F3_BLT  && $signed(alu_op1_fwd) < $signed(alu_op2_fwd)) || 
      (x_funct3 == F3_BGE  && $signed(alu_op1_fwd) >= $signed(alu_op2_fwd))|| 
      (x_funct3 == F3_BLTU && alu_op1_fwd < alu_op2_fwd)  || 
      (x_funct3 == F3_BGEU && alu_op1_fwd >= alu_op2_fwd)    
    ));
    assign branch_taken = branch_cond || x_jal || x_jalr;
    assign branch_target = (x_jalr) ? (alu_op1_fwd + x_imm) : (x_pc + x_imm);

    // EX/MEM Update
    always @(posedge clk) begin
        if (rst) begin m_reg_we <= 0; m_mem_we <= 0; end
        else begin
            m_reg_we <= (x_is_div_op) ? 0 : x_reg_we; 
            m_mem_we <= x_mem_we;
            m_pc <= x_pc;
            m_alu_result <= (x_jal || x_jalr) ? (x_pc + 4) : alu_result;
            m_store_data <= alu_op2_fwd;
            m_rd_addr <= x_rd_addr;
            m_rs2_addr <= x_rs2_addr; // Support WM bypass
            m_load <= x_load;
            m_funct3 <= x_funct3; // Pass funct3
            m_inst <= x_inst;
        end
    end

  /****************/
  /* MEMORY STAGE */
  /****************/

    // WM Bypass (writeback -> memory) for store
    reg [`REG_SIZE:0] final_store_data;
    always @(*) begin
        if (w_reg_we && w_rd_addr != 0 && w_rd_addr == m_rs2_addr) final_store_data = wb_data;
        else final_store_data = m_store_data;
    end
    
    reg [3:0] mem_mask;
    always @(*) begin
        if (m_mem_we) begin
            case (m_funct3)
               3'b000: begin // SB
                   if (m_alu_result[1:0] == 0) mem_mask = 4'b0001;
                   else if (m_alu_result[1:0] == 1) mem_mask = 4'b0010;
                   else if (m_alu_result[1:0] == 2) mem_mask = 4'b0100;
                   else mem_mask = 4'b1000;
               end
               3'b001: begin // SH
                   if (m_alu_result[1] == 0) mem_mask = 4'b0011;
                   else mem_mask = 4'b1100;
               end
               default: mem_mask = 4'b1111; // SW
            endcase
        end else mem_mask = 4'b0000;
    end

    always @(*) begin
        addr_to_dmem = m_alu_result;
        store_we_to_dmem = mem_mask;
        // store data shift (Alignment)
        if (m_funct3 == 3'b000) store_data_to_dmem = {4{final_store_data[7:0]}}; // Copy byte to all positions
        else if (m_funct3 == 3'b001) store_data_to_dmem = {2{final_store_data[15:0]}};
        else store_data_to_dmem = final_store_data;
    end

    // Update MEM/WB
    always @(posedge clk) begin
        if (rst) begin 
            w_reg_we <= 0; 
            w_inst <= 0; 
        end
        else begin
            w_pc <= m_pc; 
            w_alu_result <= m_alu_result; 
            w_mem_data <= load_data_from_dmem;
            w_rd_addr <= m_rd_addr; 
            w_reg_we <= m_reg_we; 
            w_load <= m_load;
            w_funct3 <= m_funct3;
            w_byte_offset <= m_alu_result[1:0]; // Lưu offset để cắt Load Data
            w_inst <= m_inst;
        end
    end

  /****************/
  /* WRITEBACK STAGE */
  /****************/

    reg [`REG_SIZE:0] processed_load_data;
    reg [7:0] lb_byte;
    reg [15:0] lh_half;
    
    always @(*) begin
        // Extract Byte
        case (w_byte_offset)
            2'b00: lb_byte = w_mem_data[7:0];
            2'b01: lb_byte = w_mem_data[15:8];
            2'b10: lb_byte = w_mem_data[23:16];
            2'b11: lb_byte = w_mem_data[31:24];
        endcase
        // Extract Half
        case (w_byte_offset[1])
            1'b0: lh_half = w_mem_data[15:0];
            1'b1: lh_half = w_mem_data[31:16];
        endcase
        
        // Sign/Zero Extension based on funct3
        case (w_funct3)
            3'b000: processed_load_data = {{24{lb_byte[7]}}, lb_byte}; // LB
            3'b001: processed_load_data = {{16{lh_half[15]}}, lh_half}; // LH
            3'b100: processed_load_data = {24'b0, lb_byte}; // LBU
            3'b101: processed_load_data = {16'b0, lh_half}; // LHU
            default: processed_load_data = w_mem_data; // LW
        endcase
    end

    assign wb_data = (w_load) ? processed_load_data : w_alu_result;

    // Divider Result Selection
    wire div_valid   = div_busy[7][6];
    wire div_get_rem = div_busy[7][5];
    wire [4:0] div_dst = div_busy[7][4:0];
    wire final_rf_we = w_reg_we || div_valid; 
    
    reg [4:0] final_rf_dst;
    reg [`REG_SIZE:0] final_rf_data;

    always @(*) begin
        if (div_valid) begin
            final_rf_dst = div_dst;
            final_rf_data = (div_get_rem) ? div_remainder : div_quotient;
        end else begin
            final_rf_dst = w_rd_addr;
            final_rf_data = wb_data;
        end
    end

    // Trace
    always @(*) begin
        trace_writeback_pc = w_pc;
        trace_writeback_inst = w_inst;
        if (w_inst == 0) trace_writeback_pc = 0;
    end

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
    $readmemh("E:/test.hex", mem_array);
  end



  localparam AddrMsb = $clog2(NUM_WORDS) + 1;
  localparam AddrLsb = 2;

  always @(negedge clk) begin
    inst_from_imem <= mem_array[{pc_to_imem[AddrMsb:AddrLsb]}];
  end
    
    assign load_data_from_dmem = mem_array[{addr_to_dmem[AddrMsb:AddrLsb]}];

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
