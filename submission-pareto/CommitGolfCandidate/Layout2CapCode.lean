import CommitGolfCandidate.Layout2QuartetCode
import CommitGolfCandidate.Layout2Views
namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Layout2.Quartet (checkImage run_control)
open TwoPermutationPrototype.Opening (getReg_setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 1300000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
attribute [local simp] zero mem_pc pc_pc mem_reg pc_ite reg_ite mem_ite
theorem capCode1002 : (checkImage.code[1002]?).bind decodeInstruction=some (.base (.ADDI .x6 .x0 534)) := rfl
theorem capCode1003 : (checkImage.code[1003]?).bind decodeInstruction=some (.base (.MUL .x6 .x16 .x6)) := rfl
theorem capCode1004 : (checkImage.code[1004]?).bind decodeInstruction=some (.base (.BLTU .x17 .x6 5632)) := rfl
theorem capCode1005 : (checkImage.code[1005]?).bind decodeInstruction=some (.base (.BEQ .x16 .x0 596)) := rfl
theorem capCode1006 : (checkImage.code[1006]?).bind decodeInstruction=some (.base (.ADD .x8 .x15 .x6)) := rfl
theorem capCode1007 : (checkImage.code[1007]?).bind decodeInstruction=some (.base (.SUB .x9 .x17 .x6)) := rfl
theorem capCode1008 : (checkImage.code[1008]?).bind decodeInstruction=some (.base (.ADDI .x20 .x0 952)) := rfl
theorem capCode1009 : (checkImage.code[1009]?).bind decodeInstruction=some (.base (.ADDI .x21 .x0 8)) := rfl
theorem capCode1010 : (checkImage.code[1010]?).bind decodeInstruction=some (.base (.BLTU .x9 .x20 36)) := rfl
theorem capCode1011 : (checkImage.code[1011]?).bind decodeInstruction=some (.base (.ADDI .x18 .x0 952)) := rfl
theorem capCode1012 : (checkImage.code[1012]?).bind decodeInstruction=some (.base (.LUI .x19 21)) := rfl
theorem capCode1013 : (checkImage.code[1013]?).bind decodeInstruction=some (.base (.ADDI .x19 .x19 3776)) := rfl
theorem capCode1014 : (checkImage.code[1014]?).bind decodeInstruction=some (.base (.ADD .x19 .x19 .x2)) := rfl
theorem capCode1015 : (checkImage.code[1015]?).bind decodeInstruction=some (.base (.JAL .x31 2096128)) := rfl
theorem capCode1016 : (checkImage.code[1016]?).bind decodeInstruction=some (.base (.ADDI .x8 .x8 952)) := rfl
theorem capCode1017 : (checkImage.code[1017]?).bind decodeInstruction=some (.base (.ADDI .x9 .x9 3144)) := rfl
theorem capCode1018 : (checkImage.code[1018]?).bind decodeInstruction=some (.base (.JAL .x0 2097120)) := rfl
theorem capCode1019 : (checkImage.code[1019]?).bind decodeInstruction=some (.base (.ADDI .x5 .x9 6)) := rfl
theorem capCode1020 : (checkImage.code[1020]?).bind decodeInstruction=some (.base (.ADDI .x6 .x0 30)) := rfl
theorem capCode1021 : (checkImage.code[1021]?).bind decodeInstruction=some (.base (.DIVU .x5 .x5 .x6)) := rfl
theorem capCode1022 : (checkImage.code[1022]?).bind decodeInstruction=some (.base (.SLLI .x5 .x5 3)) := rfl
theorem capCode1023 : (checkImage.code[1023]?).bind decodeInstruction=some (.base (.LUI .x19 21)) := rfl
theorem capCode1024 : (checkImage.code[1024]?).bind decodeInstruction=some (.base (.ADDI .x19 .x19 3520)) := rfl
theorem capCode1025 : (checkImage.code[1025]?).bind decodeInstruction=some (.base (.ADD .x19 .x19 .x2)) := rfl
theorem capCode1026 : (checkImage.code[1026]?).bind decodeInstruction=some (.base (.ADD .x19 .x19 .x5)) := rfl
theorem capCode1027 : (checkImage.code[1027]?).bind decodeInstruction=some (.base (.LHU .x6 .x19 0)) := rfl
theorem capCode1028 : (checkImage.code[1028]?).bind decodeInstruction=some (.base (.BNE .x6 .x9 5536)) := rfl
theorem capCode1029 : (checkImage.code[1029]?).bind decodeInstruction=some (.base (.BEQ .x9 .x0 20)) := rfl
theorem capCode1030 : (checkImage.code[1030]?).bind decodeInstruction=some (.base (.LWU .x6 .x19 4)) := rfl
theorem capCode1031 : (checkImage.code[1031]?).bind decodeInstruction=some (.base (.ADD .x19 .x2 .x6)) := rfl
theorem capCode1032 : (checkImage.code[1032]?).bind decodeInstruction=some (.base (.ADDI .x18 .x9 0)) := rfl
theorem capCode1033 : (checkImage.code[1033]?).bind decodeInstruction=some (.base (.JAL .x31 2096056)) := rfl
theorem capCode1153 : (checkImage.code[1153]?).bind decodeInstruction=some (.base (.JAL .x0 2096544)) := rfl
theorem capCode1154 : (checkImage.code[1154]?).bind decodeInstruction=some (.base (.BNE .x17 .x0 5032)) := rfl
theorem capCode1155 : (checkImage.code[1155]?).bind decodeInstruction=some (.base (.JAL .x0 2096536)) := rfl

end CommitGolfCandidate.Layout2.Cap
