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
theorem effects_copyHead (s : MachineState) (here : s.pc=pc Block.copyHead.start) :
    (∀ r, (after .copyHead s).getReg r=regOut s r .copyHead) ∧
    (after .copyHead s).mem=(memOut s .copyHead).mem ∧
    (after .copyHead s).pc=pcOut s .copyHead ∧ (Ready s Block.copyHead.ops ↔ accessible s .copyHead) := by
  have hpc0 : s.pc=pc 759 := here
  let u1 := execInstrBr s (.ADDI .x5 .x8 0)
  have hr1 (r : Reg) : u1.getReg r=if .x5=r then (s.getReg .x8) else s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 760) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  let u2 := execInstrBr u1 (.ADDI .x6 .x10 0)
  have hr2 (r : Reg) : u2.getReg r=if .x6=r then (s.getReg .x10) else if .x5=r then (s.getReg .x8) else s.getReg r := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hm2 : u2.mem=s.mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(pc 761) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  let u3 := execInstrBr u2 (.ADD .x7 .x8 .x18)
  have hr3 (r : Reg) : u3.getReg r=if .x7=r then ((s.getReg .x8) + (s.getReg .x18)) else if .x6=r then (s.getReg .x10) else if .x5=r then (s.getReg .x8) else s.getReg r := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hm3 : u3.mem=s.mem := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hpc3 : u3.pc=(pc 762) := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  refine ⟨hr3,hm3,hpc3,?_⟩
  change (memoryArgumentsValid s (.ADDI .x5 .x8 0)=true ∧ memoryArgumentsValid u1 (.ADDI .x6 .x10 0)=true ∧ memoryArgumentsValid u2 (.ADD .x7 .x8 .x18)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_copyByte (s : MachineState) (here : s.pc=pc Block.copyByte.start) :
    (∀ r, (after .copyByte s).getReg r=regOut s r .copyByte) ∧
    (after .copyByte s).mem=(memOut s .copyByte).mem ∧
    (after .copyByte s).pc=pcOut s .copyByte ∧ (Ready s Block.copyByte.ops ↔ accessible s .copyByte) := by
  have hpc0 : s.pc=pc 762 := here
  let u1 := execInstrBr s (.LBU .x28 .x5 0)
  have hr1 (r : Reg) : u1.getReg r=if .x28=r then ((s.getByte (s.getReg .x5)).zeroExtend 64) else s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 763) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have ha1 : (memoryArgumentsValid s (.LBU .x28 .x5 0)=true) ↔ (accessValid (s.getReg .x5) 1=true) := by
    simp [memoryArgumentsValid,memAccess,u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc]
  let u2 := execInstrBr u1 (.SB .x6 .x28 0)
  have hr2 (r : Reg) : u2.getReg r=if .x28=r then ((s.getByte (s.getReg .x5)).zeroExtend 64) else s.getReg r := by
    simp only [u2,execInstrBr,MachineState.getReg_setPC,reg_byte,reg_word] <;> exact hr1 r
  have hm2 : u2.mem=(s.setByte (s.getReg .x6) (((s.getByte (s.getReg .x5)).zeroExtend 64).truncate 8)).mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(pc 764) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have ha2 : (memoryArgumentsValid u1 (.SB .x6 .x28 0)=true) ↔ (accessValid (s.getReg .x6) 1=true) := by
    simp [memoryArgumentsValid,memAccess,u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc]
  let u3 := execInstrBr u2 (.ADDI .x5 .x5 1)
  have hr3 (r : Reg) : u3.getReg r=if .x5=r then ((s.getReg .x5) + 1#64) else if .x28=r then ((s.getByte (s.getReg .x5)).zeroExtend 64) else s.getReg r := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hm3 : u3.mem=(s.setByte (s.getReg .x6) (((s.getByte (s.getReg .x5)).zeroExtend 64).truncate 8)).mem := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hpc3 : u3.pc=(pc 765) := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  let u4 := execInstrBr u3 (.ADDI .x6 .x6 1)
  have hr4 (r : Reg) : u4.getReg r=if .x6=r then ((s.getReg .x6) + 1#64) else if .x5=r then ((s.getReg .x5) + 1#64) else if .x28=r then ((s.getByte (s.getReg .x5)).zeroExtend 64) else s.getReg r := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  have hm4 : u4.mem=(s.setByte (s.getReg .x6) (((s.getByte (s.getReg .x5)).zeroExtend 64).truncate 8)).mem := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  have hpc4 : u4.pc=(pc 766) := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  let u5 := execInstrBr u4 (.BNE .x5 .x7 8176)
  have hr5 (r : Reg) : u5.getReg r=if .x6=r then ((s.getReg .x6) + 1#64) else if .x5=r then ((s.getReg .x5) + 1#64) else if .x28=r then ((s.getByte (s.getReg .x5)).zeroExtend 64) else s.getReg r := by
    simp +contextual [u5,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr4,hm4,hpc4,BitVec.add_assoc] <;> try rfl
  have hm5 : u5.mem=(s.setByte (s.getReg .x6) (((s.getByte (s.getReg .x5)).zeroExtend 64).truncate 8)).mem := by
    simp +contextual [u5,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr4,hm4,hpc4,BitVec.add_assoc] <;> try rfl
  have hpc5 : u5.pc=(if ((s.getReg .x5) + 1#64) != (s.getReg .x7) then pc 762 else pc 767) := by
    simp +contextual [u5,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr4,hm4,hpc4,BitVec.add_assoc] <;> try rfl
  refine ⟨hr5,hm5,hpc5,?_⟩
  change (memoryArgumentsValid s (.LBU .x28 .x5 0)=true ∧ memoryArgumentsValid u1 (.SB .x6 .x28 0)=true ∧ memoryArgumentsValid u2 (.ADDI .x5 .x5 1)=true ∧ memoryArgumentsValid u3 (.ADDI .x6 .x6 1)=true ∧ memoryArgumentsValid u4 (.BNE .x5 .x7 8176)=true ∧ True) ↔ _
  simp only [ha1,ha2, accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_writeHead (s : MachineState) (here : s.pc=pc Block.writeHead.start) :
    (∀ r, (after .writeHead s).getReg r=regOut s r .writeHead) ∧
    (after .writeHead s).mem=(memOut s .writeHead).mem ∧
    (after .writeHead s).pc=pcOut s .writeHead ∧ (Ready s Block.writeHead.ops ↔ accessible s .writeHead) := by
  have hpc0 : s.pc=pc 767 := here
  let u1 := execInstrBr s (.ADDI .x5 .x8 0)
  have hr1 (r : Reg) : u1.getReg r=if .x5=r then (s.getReg .x8) else s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 768) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  refine ⟨hr1,hm1,hpc1,?_⟩
  change (memoryArgumentsValid s (.ADDI .x5 .x8 0)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_byteHead (s : MachineState) (here : s.pc=pc Block.byteHead.start) :
    (∀ r, (after .byteHead s).getReg r=regOut s r .byteHead) ∧
    (after .byteHead s).mem=(memOut s .byteHead).mem ∧
    (after .byteHead s).pc=pcOut s .byteHead ∧ (Ready s Block.byteHead.ops ↔ accessible s .byteHead) := by
  have hpc0 : s.pc=pc 768 := here
  let u1 := execInstrBr s (.ADDI .x6 .x0 0)
  have hr1 (r : Reg) : u1.getReg r=if .x6=r then 0#64 else s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 769) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  let u2 := execInstrBr u1 (.ADDI .x28 .x0 0)
  have hr2 (r : Reg) : u2.getReg r=if .x28=r then 0#64 else if .x6=r then 0#64 else s.getReg r := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hm2 : u2.mem=s.mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(pc 770) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  refine ⟨hr2,hm2,hpc2,?_⟩
  change (memoryArgumentsValid s (.ADDI .x6 .x0 0)=true ∧ memoryArgumentsValid u1 (.ADDI .x28 .x0 0)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

end CommitGolfCandidate.Layout2
