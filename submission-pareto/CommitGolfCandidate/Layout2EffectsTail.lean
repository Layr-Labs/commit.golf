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
theorem effects_one (s : MachineState) (here : s.pc=pc Block.one.start) :
    (∀ r, (after .one s).getReg r=regOut s r .one) ∧
    (after .one s).mem=(memOut s .one).mem ∧
    (after .one s).pc=pcOut s .one ∧ (Ready s Block.one.ops ↔ accessible s .one) := by
  have hpc0 : s.pc=pc 722 := here
  let u1 := execInstrBr s (.ADDI .x5 .x0 1)
  have hr1 (r : Reg) : u1.getReg r=if .x5=r then 1#64 else s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 723) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  let u2 := execInstrBr u1 (.BEQ .x9 .x5 44)
  have hr2 (r : Reg) : u2.getReg r=if .x5=r then 1#64 else s.getReg r := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hm2 : u2.mem=s.mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(if (s.getReg .x9) == 1#64 then pc 734 else pc 724) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  refine ⟨hr2,hm2,hpc2,?_⟩
  change (memoryArgumentsValid s (.ADDI .x5 .x0 1)=true ∧ memoryArgumentsValid u1 (.BEQ .x9 .x5 44)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_two (s : MachineState) (here : s.pc=pc Block.two.start) :
    (∀ r, (after .two s).getReg r=regOut s r .two) ∧
    (after .two s).mem=(memOut s .two).mem ∧
    (after .two s).pc=pcOut s .two ∧ (Ready s Block.two.ops ↔ accessible s .two) := by
  have hpc0 : s.pc=pc 724 := here
  let u1 := execInstrBr s (.ADDI .x5 .x0 2)
  have hr1 (r : Reg) : u1.getReg r=if .x5=r then 2#64 else s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 725) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  let u2 := execInstrBr u1 (.BEQ .x9 .x5 20)
  have hr2 (r : Reg) : u2.getReg r=if .x5=r then 2#64 else s.getReg r := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hm2 : u2.mem=s.mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(if (s.getReg .x9) == 2#64 then pc 730 else pc 726) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  refine ⟨hr2,hm2,hpc2,?_⟩
  change (memoryArgumentsValid s (.ADDI .x5 .x0 2)=true ∧ memoryArgumentsValid u1 (.BEQ .x9 .x5 20)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_three (s : MachineState) (here : s.pc=pc Block.three.start) :
    (∀ r, (after .three s).getReg r=regOut s r .three) ∧
    (after .three s).mem=(memOut s .three).mem ∧
    (after .three s).pc=pcOut s .three ∧ (Ready s Block.three.ops ↔ accessible s .three) := by
  have hpc0 : s.pc=pc 726 := here
  let u1 := execInstrBr s (.ADDI .x18 .x0 1602)
  have hr1 (r : Reg) : u1.getReg r=if .x18=r then 1602#64 else s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 727) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  let u2 := execInstrBr u1 (.LUI .x5 15)
  have hr2 (r : Reg) : u2.getReg r=if .x5=r then 61440#64 else if .x18=r then 1602#64 else s.getReg r := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hm2 : u2.mem=s.mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(pc 728) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  let u3 := execInstrBr u2 (.ADDI .x5 .x5 2464)
  have hr3 (r : Reg) : u3.getReg r=if .x5=r then (61440#64 + (signExtend12 2464)) else if .x18=r then 1602#64 else s.getReg r := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hm3 : u3.mem=s.mem := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hpc3 : u3.pc=(pc 729) := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  let u4 := execInstrBr u3 (.JAL .x0 32)
  have hr4 (r : Reg) : u4.getReg r=if .x5=r then (61440#64 + (signExtend12 2464)) else if .x18=r then 1602#64 else s.getReg r := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  have hm4 : u4.mem=s.mem := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  have hpc4 : u4.pc=(pc 737) := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  refine ⟨hr4,hm4,hpc4,?_⟩
  change (memoryArgumentsValid s (.ADDI .x18 .x0 1602)=true ∧ memoryArgumentsValid u1 (.LUI .x5 15)=true ∧ memoryArgumentsValid u2 (.ADDI .x5 .x5 2464)=true ∧ memoryArgumentsValid u3 (.JAL .x0 32)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_pair (s : MachineState) (here : s.pc=pc Block.pair.start) :
    (∀ r, (after .pair s).getReg r=regOut s r .pair) ∧
    (after .pair s).mem=(memOut s .pair).mem ∧
    (after .pair s).pc=pcOut s .pair ∧ (Ready s Block.pair.ops ↔ accessible s .pair) := by
  have hpc0 : s.pc=pc 730 := here
  let u1 := execInstrBr s (.ADDI .x18 .x0 1068)
  have hr1 (r : Reg) : u1.getReg r=if .x18=r then 1068#64 else s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 731) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  let u2 := execInstrBr u1 (.LUI .x5 10)
  have hr2 (r : Reg) : u2.getReg r=if .x5=r then 40960#64 else if .x18=r then 1068#64 else s.getReg r := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hm2 : u2.mem=s.mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(pc 732) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  let u3 := execInstrBr u2 (.ADDI .x5 .x5 1760)
  have hr3 (r : Reg) : u3.getReg r=if .x5=r then (40960#64 + 1760#64) else if .x18=r then 1068#64 else s.getReg r := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hm3 : u3.mem=s.mem := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hpc3 : u3.pc=(pc 733) := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  let u4 := execInstrBr u3 (.JAL .x0 16)
  have hr4 (r : Reg) : u4.getReg r=if .x5=r then (40960#64 + 1760#64) else if .x18=r then 1068#64 else s.getReg r := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  have hm4 : u4.mem=s.mem := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  have hpc4 : u4.pc=(pc 737) := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  refine ⟨hr4,hm4,hpc4,?_⟩
  change (memoryArgumentsValid s (.ADDI .x18 .x0 1068)=true ∧ memoryArgumentsValid u1 (.LUI .x5 10)=true ∧ memoryArgumentsValid u2 (.ADDI .x5 .x5 1760)=true ∧ memoryArgumentsValid u3 (.JAL .x0 16)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_single (s : MachineState) (here : s.pc=pc Block.single.start) :
    (∀ r, (after .single s).getReg r=regOut s r .single) ∧
    (after .single s).mem=(memOut s .single).mem ∧
    (after .single s).pc=pcOut s .single ∧ (Ready s Block.single.ops ↔ accessible s .single) := by
  have hpc0 : s.pc=pc 734 := here
  let u1 := execInstrBr s (.ADDI .x18 .x0 534)
  have hr1 (r : Reg) : u1.getReg r=if .x18=r then 534#64 else s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 735) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  let u2 := execInstrBr u1 (.LUI .x5 8)
  have hr2 (r : Reg) : u2.getReg r=if .x5=r then 32768#64 else if .x18=r then 534#64 else s.getReg r := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hm2 : u2.mem=s.mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(pc 736) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  let u3 := execInstrBr u2 (.ADDI .x5 .x5 1408)
  have hr3 (r : Reg) : u3.getReg r=if .x5=r then (32768#64 + 1408#64) else if .x18=r then 534#64 else s.getReg r := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hm3 : u3.mem=s.mem := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hpc3 : u3.pc=(pc 737) := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  refine ⟨hr3,hm3,hpc3,?_⟩
  change (memoryArgumentsValid s (.ADDI .x18 .x0 534)=true ∧ memoryArgumentsValid u1 (.LUI .x5 8)=true ∧ memoryArgumentsValid u2 (.ADDI .x5 .x5 1408)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_callTail (s : MachineState) (here : s.pc=pc Block.callTail.start) :
    (∀ r, (after .callTail s).getReg r=regOut s r .callTail) ∧
    (after .callTail s).mem=(memOut s .callTail).mem ∧
    (after .callTail s).pc=pcOut s .callTail ∧ (Ready s Block.callTail.ops ↔ accessible s .callTail) := by
  have hpc0 : s.pc=pc 737 := here
  let u1 := execInstrBr s (.ADD .x19 .x2 .x5)
  have hr1 (r : Reg) : u1.getReg r=if .x19=r then ((s.getReg .x2) + (s.getReg .x5)) else s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 738) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  let u2 := execInstrBr u1 (.JAL .x31 84)
  have hr2 (r : Reg) : u2.getReg r=if .x31=r then (pc 739) else if .x19=r then ((s.getReg .x2) + (s.getReg .x5)) else s.getReg r := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hm2 : u2.mem=s.mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(pc 759) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  refine ⟨hr2,hm2,hpc2,?_⟩
  change (memoryArgumentsValid s (.ADD .x19 .x2 .x5)=true ∧ memoryArgumentsValid u1 (.JAL .x31 84)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_clearHead (s : MachineState) (here : s.pc=pc Block.clearHead.start) :
    (∀ r, (after .clearHead s).getReg r=regOut s r .clearHead) ∧
    (after .clearHead s).mem=(memOut s .clearHead).mem ∧
    (after .clearHead s).pc=pcOut s .clearHead ∧ (Ready s Block.clearHead.ops ↔ accessible s .clearHead) := by
  have hpc0 : s.pc=pc 739 := here
  let u1 := execInstrBr s (.ADDI .x5 .x10 0)
  have hr1 (r : Reg) : u1.getReg r=if .x5=r then (s.getReg .x10) else s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 740) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  let u2 := execInstrBr u1 (.ADDI .x6 .x10 2047)
  have hr2 (r : Reg) : u2.getReg r=if .x6=r then ((s.getReg .x10) + 2047#64) else if .x5=r then (s.getReg .x10) else s.getReg r := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hm2 : u2.mem=s.mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(pc 741) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  let u3 := execInstrBr u2 (.ADDI .x6 .x6 89)
  have hr3 (r : Reg) : u3.getReg r=if .x6=r then (((s.getReg .x10) + 2047#64) + 89#64) else if .x5=r then (s.getReg .x10) else s.getReg r := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hm3 : u3.mem=s.mem := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hpc3 : u3.pc=(pc 742) := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  refine ⟨hr3,hm3,hpc3,?_⟩
  change (memoryArgumentsValid s (.ADDI .x5 .x10 0)=true ∧ memoryArgumentsValid u1 (.ADDI .x6 .x10 2047)=true ∧ memoryArgumentsValid u2 (.ADDI .x6 .x6 89)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

end CommitGolfCandidate.Layout2
