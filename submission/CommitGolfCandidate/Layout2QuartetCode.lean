import CommitGolfCandidate.Layout2QuartetBytes
namespace CommitGolfCandidate.Layout2.Quartet
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 10000
theorem code0 : (checkImage.code[1001]?).bind decodeInstruction=some (.base (.JAL .x0 2096296)) := rfl
theorem code787 : (checkImage.code[787]?).bind decodeInstruction=some (.base (.ADDI .x6 .x0 534)) := rfl
theorem code788 : (checkImage.code[788]?).bind decodeInstruction=some (.base (.MUL .x6 .x16 .x6)) := rfl
theorem code789 : (checkImage.code[789]?).bind decodeInstruction=some (.base (.BLTU .x17 .x6 6492)) := rfl
theorem code790 : (checkImage.code[790]?).bind decodeInstruction=some (.base (.BEQ .x16 .x0 8176)) := rfl
theorem code791 : (checkImage.code[791]?).bind decodeInstruction=some (.base (.ADDI .x8 .x15 0)) := rfl
theorem code792 : (checkImage.code[792]?).bind decodeInstruction=some (.base (.ADDI .x9 .x13 0)) := rfl
theorem code793 : (checkImage.code[793]?).bind decodeInstruction=some (.base (.ADDI .x18 .x16 0)) := rfl
theorem code794 : (checkImage.code[794]?).bind decodeInstruction=some (.base (.ADDI .x19 .x0 0)) := rfl
theorem code795 : (checkImage.code[795]?).bind decodeInstruction=some (.base (.LD .x5 .x9 0)) := rfl
theorem code796 : (checkImage.code[796]?).bind decodeInstruction=some (.base (.ANDI .x5 .x5 3)) := rfl
theorem code797 : (checkImage.code[797]?).bind decodeInstruction=some (.base (.BEQ .x5 .x0 28)) := rfl
theorem code798 : (checkImage.code[798]?).bind decodeInstruction=some (.base (.ADDI .x5 .x5 4095)) := rfl
theorem code799 : (checkImage.code[799]?).bind decodeInstruction=some (.base (.BEQ .x5 .x0 208)) := rfl
theorem code800 : (checkImage.code[800]?).bind decodeInstruction=some (.base (.ADDI .x5 .x5 4095)) := rfl
theorem code801 : (checkImage.code[801]?).bind decodeInstruction=some (.base (.BEQ .x5 .x0 388)) := rfl
theorem code802 : (checkImage.code[802]?).bind decodeInstruction=some (.base (.ADDI .x5 .x5 4095)) := rfl
theorem code803 : (checkImage.code[803]?).bind decodeInstruction=some (.base (.JAL .x0 568)) := rfl
theorem code850 : (checkImage.code[850]?).bind decodeInstruction=some (.base (.JAL .x0 568)) := rfl
theorem code897 : (checkImage.code[897]?).bind decodeInstruction=some (.base (.JAL .x0 380)) := rfl
theorem code944 : (checkImage.code[944]?).bind decodeInstruction=some (.base (.JAL .x0 192)) := rfl
theorem code991 : (checkImage.code[991]?).bind decodeInstruction=some (.base (.JAL .x0 4)) := rfl
theorem code992 : (checkImage.code[992]?).bind decodeInstruction=some (.base (.ADDI .x18 .x18 4095)) := rfl
theorem code993 : (checkImage.code[993]?).bind decodeInstruction=some (.base (.BEQ .x18 .x0 7364)) := rfl
theorem code994 : (checkImage.code[994]?).bind decodeInstruction=some (.base (.ADDI .x9 .x9 8)) := rfl
theorem code995 : (checkImage.code[995]?).bind decodeInstruction=some (.base (.ADDI .x8 .x8 536)) := rfl
theorem code996 : (checkImage.code[996]?).bind decodeInstruction=some (.base (.BNE .x19 .x0 8)) := rfl
theorem code997 : (checkImage.code[997]?).bind decodeInstruction=some (.base (.ADDI .x8 .x8 4088)) := rfl
theorem code998 : (checkImage.code[998]?).bind decodeInstruction=some (.base (.ADDI .x19 .x19 1)) := rfl
theorem code999 : (checkImage.code[999]?).bind decodeInstruction=some (.base (.ANDI .x19 .x19 3)) := rfl
theorem code1000 : (checkImage.code[1000]?).bind decodeInstruction=some (.base (.JAL .x0 2096332)) := rfl

theorem run_control (I : Image) (s : MachineState) (w : Nat) (op : Instr) (cycles : Nat)
    (bound : w<2^40) (here : s.pc=pc w) (code : (I.code[w]?).bind decodeInstruction=some (.base op))
    (step : ordinaryStep s (.base op)=some (execInstrBr s op)) (price : instructionCycles (.base op)=cycles) :
    Runs I s (execInstrBr s op) 1 cycles := by
  have f:=wide_image_fetch I s w op bound here code
  intro fuel;rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ f step,price]

end CommitGolfCandidate.Layout2.Quartet
