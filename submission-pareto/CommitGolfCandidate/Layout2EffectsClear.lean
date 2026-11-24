import CommitGolfCandidate.Layout2Views
namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.Opening (getReg_setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local simp] zero mem_pc pc_pc mem_reg reg_byte reg_word pc_ite reg_ite mem_ite
theorem effects_clearCell (s : MachineState) (here : s.pc=pc Block.clearCell.start) :
    (∀ r, (after .clearCell s).getReg r=regOut s r .clearCell) ∧
    (after .clearCell s).mem=(memOut s .clearCell).mem ∧
    (after .clearCell s).pc=pcOut s .clearCell ∧ (Ready s Block.clearCell.ops ↔ accessible s .clearCell) := by
  have hpc0 : s.pc=pc 742 := here
  let u1 := execInstrBr s (.SD .x5 .x0 0)
  have hr1 (r : Reg) : u1.getReg r=s.getReg r := by
    simp only [u1,execInstrBr,MachineState.getReg_setPC,reg_byte,reg_word] <;> rfl
  have hm1 : u1.mem=(s.setMem (s.getReg .x5) 0#64).mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 743) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have ha1 : (memoryArgumentsValid s (.SD .x5 .x0 0)=true) ↔ (accessValid (s.getReg .x5) 8=true) := by
    simp [memoryArgumentsValid,memAccess,u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc]
  let u2 := execInstrBr u1 (.ADDI .x5 .x5 8)
  have hr2 (r : Reg) : u2.getReg r=if .x5=r then ((s.getReg .x5) + 8#64) else s.getReg r := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hm2 : u2.mem=(s.setMem (s.getReg .x5) 0#64).mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(pc 744) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  let u3 := execInstrBr u2 (.BNE .x5 .x6 8184)
  have hr3 (r : Reg) : u3.getReg r=if .x5=r then ((s.getReg .x5) + 8#64) else s.getReg r := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hm3 : u3.mem=(s.setMem (s.getReg .x5) 0#64).mem := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hpc3 : u3.pc=(if ((s.getReg .x5) + 8#64) != (s.getReg .x6) then pc 742 else pc 745) := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  refine ⟨hr3,hm3,hpc3,?_⟩
  change (memoryArgumentsValid s (.SD .x5 .x0 0)=true ∧ memoryArgumentsValid u1 (.ADDI .x5 .x5 8)=true ∧ memoryArgumentsValid u2 (.BNE .x5 .x6 8184)=true ∧ True) ↔ _
  simp only [ha1, accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_restore (s : MachineState) (here : s.pc=pc Block.restore.start) :
    (∀ r, (after .restore s).getReg r=regOut s r .restore) ∧
    (after .restore s).mem=(memOut s .restore).mem ∧
    (after .restore s).pc=pcOut s .restore ∧ (Ready s Block.restore.ops ↔ accessible s .restore) := by
  refine ⟨?_,rfl,?_,?_⟩
  · intro r;cases r <;> rfl
  · change s.pc+4+4+4+4+4+4+4+4+4+4+4+4+4+signExtend21 2094124=pc 1
    rw [here];rfl
  · exact ⟨fun _=>trivial, fun _=>by repeat' first | constructor | rfl⟩

end CommitGolfCandidate.Layout2
