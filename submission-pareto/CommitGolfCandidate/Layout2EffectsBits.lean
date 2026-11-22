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
theorem effects_bitStep (s : MachineState) (here : s.pc=pc Block.bitStep.start) :
    (∀ r, (after .bitStep s).getReg r=regOut s r .bitStep) ∧
    (after .bitStep s).mem=(memOut s .bitStep).mem ∧
    (after .bitStep s).pc=pcOut s .bitStep ∧ (Ready s Block.bitStep.ops ↔ accessible s .bitStep) := by
  have hpc0 : s.pc=pc 770 := here
  let u1 := execInstrBr s (.LHU .x29 .x19 0)
  have hr1 (r : Reg) : u1.getReg r=if .x29=r then ((s.getHalfword (s.getReg .x19)).zeroExtend 64) else s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 771) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have ha1 : (memoryArgumentsValid s (.LHU .x29 .x19 0)=true) ↔ (accessValid (s.getReg .x19) 2=true) := by
    simp [memoryArgumentsValid,memAccess,u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc]
  let u2 := execInstrBr u1 (.SRLI .x30 .x29 3)
  have hr2 (r : Reg) : u2.getReg r=if .x30=r then (((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) else if .x29=r then ((s.getHalfword (s.getReg .x19)).zeroExtend 64) else s.getReg r := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hm2 : u2.mem=s.mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(pc 772) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  let u3 := execInstrBr u2 (.ADD .x30 .x30 .x10)
  have hr3 (r : Reg) : u3.getReg r=if .x30=r then ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10)) else if .x29=r then ((s.getHalfword (s.getReg .x19)).zeroExtend 64) else s.getReg r := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hm3 : u3.mem=s.mem := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hpc3 : u3.pc=(pc 773) := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  let u4 := execInstrBr u3 (.LBU .x30 .x30 0)
  have hr4 (r : Reg) : u4.getReg r=if .x30=r then ((s.getByte ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10))).zeroExtend 64) else if .x29=r then ((s.getHalfword (s.getReg .x19)).zeroExtend 64) else s.getReg r := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  have hm4 : u4.mem=s.mem := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  have hpc4 : u4.pc=(pc 774) := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  have ha4 : (memoryArgumentsValid u3 (.LBU .x30 .x30 0)=true) ↔ (accessValid ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10)) 1=true) := by
    simp [memoryArgumentsValid,memAccess,u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc]
  let u5 := execInstrBr u4 (.ANDI .x29 .x29 7)
  have hr5 (r : Reg) : u5.getReg r=if .x29=r then (((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64) else if .x30=r then ((s.getByte ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10))).zeroExtend 64) else s.getReg r := by
    simp +contextual [u5,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr4,hm4,hpc4,BitVec.add_assoc] <;> try rfl
  have hm5 : u5.mem=s.mem := by
    simp +contextual [u5,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr4,hm4,hpc4,BitVec.add_assoc] <;> try rfl
  have hpc5 : u5.pc=(pc 775) := by
    simp +contextual [u5,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr4,hm4,hpc4,BitVec.add_assoc] <;> try rfl
  let u6 := execInstrBr u5 (.SRL .x30 .x30 .x29)
  have hr6 (r : Reg) : u6.getReg r=if .x30=r then (((s.getByte ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10))).zeroExtend 64) >>> ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64).toNat % 64)) else if .x29=r then (((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64) else s.getReg r := by
    simp +contextual [u6,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr5,hm5,hpc5,BitVec.add_assoc] <;> try rfl
  have hm6 : u6.mem=s.mem := by
    simp +contextual [u6,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr5,hm5,hpc5,BitVec.add_assoc] <;> try rfl
  have hpc6 : u6.pc=(pc 776) := by
    simp +contextual [u6,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr5,hm5,hpc5,BitVec.add_assoc] <;> try rfl
  let u7 := execInstrBr u6 (.ANDI .x30 .x30 1)
  have hr7 (r : Reg) : u7.getReg r=if .x30=r then ((((s.getByte ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10))).zeroExtend 64) >>> ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64).toNat % 64)) &&& 1#64) else if .x29=r then (((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64) else s.getReg r := by
    simp +contextual [u7,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr6,hm6,hpc6,BitVec.add_assoc] <;> try rfl
  have hm7 : u7.mem=s.mem := by
    simp +contextual [u7,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr6,hm6,hpc6,BitVec.add_assoc] <;> try rfl
  have hpc7 : u7.pc=(pc 777) := by
    simp +contextual [u7,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr6,hm6,hpc6,BitVec.add_assoc] <;> try rfl
  let u8 := execInstrBr u7 (.SLL .x30 .x30 .x28)
  have hr8 (r : Reg) : u8.getReg r=if .x30=r then (((((s.getByte ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10))).zeroExtend 64) >>> ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64).toNat % 64)) &&& 1#64) <<< ((s.getReg .x28).toNat % 64)) else if .x29=r then (((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64) else s.getReg r := by
    simp +contextual [u8,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr7,hm7,hpc7,BitVec.add_assoc] <;> try rfl
  have hm8 : u8.mem=s.mem := by
    simp +contextual [u8,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr7,hm7,hpc7,BitVec.add_assoc] <;> try rfl
  have hpc8 : u8.pc=(pc 778) := by
    simp +contextual [u8,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr7,hm7,hpc7,BitVec.add_assoc] <;> try rfl
  let u9 := execInstrBr u8 (.OR .x6 .x6 .x30)
  have hr9 (r : Reg) : u9.getReg r=if .x6=r then ((s.getReg .x6) ||| (((((s.getByte ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10))).zeroExtend 64) >>> ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64).toNat % 64)) &&& 1#64) <<< ((s.getReg .x28).toNat % 64))) else if .x30=r then (((((s.getByte ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10))).zeroExtend 64) >>> ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64).toNat % 64)) &&& 1#64) <<< ((s.getReg .x28).toNat % 64)) else if .x29=r then (((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64) else s.getReg r := by
    simp +contextual [u9,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr8,hm8,hpc8,BitVec.add_assoc] <;> try rfl
  have hm9 : u9.mem=s.mem := by
    simp +contextual [u9,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr8,hm8,hpc8,BitVec.add_assoc] <;> try rfl
  have hpc9 : u9.pc=(pc 779) := by
    simp +contextual [u9,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr8,hm8,hpc8,BitVec.add_assoc] <;> try rfl
  let u10 := execInstrBr u9 (.ADDI .x19 .x19 2)
  have hr10 (r : Reg) : u10.getReg r=if .x19=r then ((s.getReg .x19) + 2#64) else if .x6=r then ((s.getReg .x6) ||| (((((s.getByte ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10))).zeroExtend 64) >>> ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64).toNat % 64)) &&& 1#64) <<< ((s.getReg .x28).toNat % 64))) else if .x30=r then (((((s.getByte ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10))).zeroExtend 64) >>> ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64).toNat % 64)) &&& 1#64) <<< ((s.getReg .x28).toNat % 64)) else if .x29=r then (((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64) else s.getReg r := by
    simp +contextual [u10,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr9,hm9,hpc9,BitVec.add_assoc] <;> try rfl
  have hm10 : u10.mem=s.mem := by
    simp +contextual [u10,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr9,hm9,hpc9,BitVec.add_assoc] <;> try rfl
  have hpc10 : u10.pc=(pc 780) := by
    simp +contextual [u10,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr9,hm9,hpc9,BitVec.add_assoc] <;> try rfl
  let u11 := execInstrBr u10 (.ADDI .x28 .x28 1)
  have hr11 (r : Reg) : u11.getReg r=if .x28=r then ((s.getReg .x28) + 1#64) else if .x19=r then ((s.getReg .x19) + 2#64) else if .x6=r then ((s.getReg .x6) ||| (((((s.getByte ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10))).zeroExtend 64) >>> ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64).toNat % 64)) &&& 1#64) <<< ((s.getReg .x28).toNat % 64))) else if .x30=r then (((((s.getByte ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10))).zeroExtend 64) >>> ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64).toNat % 64)) &&& 1#64) <<< ((s.getReg .x28).toNat % 64)) else if .x29=r then (((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64) else s.getReg r := by
    simp +contextual [u11,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr10,hm10,hpc10,BitVec.add_assoc] <;> try rfl
  have hm11 : u11.mem=s.mem := by
    simp +contextual [u11,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr10,hm10,hpc10,BitVec.add_assoc] <;> try rfl
  have hpc11 : u11.pc=(pc 781) := by
    simp +contextual [u11,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr10,hm10,hpc10,BitVec.add_assoc] <;> try rfl
  let u12 := execInstrBr u11 (.BNE .x28 .x21 8148)
  have hr12 (r : Reg) : u12.getReg r=if .x28=r then ((s.getReg .x28) + 1#64) else if .x19=r then ((s.getReg .x19) + 2#64) else if .x6=r then ((s.getReg .x6) ||| (((((s.getByte ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10))).zeroExtend 64) >>> ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64).toNat % 64)) &&& 1#64) <<< ((s.getReg .x28).toNat % 64))) else if .x30=r then (((((s.getByte ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) >>> (3:Nat)) + (s.getReg .x10))).zeroExtend 64) >>> ((((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64).toNat % 64)) &&& 1#64) <<< ((s.getReg .x28).toNat % 64)) else if .x29=r then (((s.getHalfword (s.getReg .x19)).zeroExtend 64) &&& 7#64) else s.getReg r := by
    simp +contextual [u12,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr11,hm11,hpc11,BitVec.add_assoc] <;> try rfl
  have hm12 : u12.mem=s.mem := by
    simp +contextual [u12,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr11,hm11,hpc11,BitVec.add_assoc] <;> try rfl
  have hpc12 : u12.pc=(if ((s.getReg .x28) + 1#64) != (s.getReg .x21) then pc 770 else pc 782) := by
    simp +contextual [u12,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr11,hm11,hpc11,BitVec.add_assoc] <;> try rfl
  refine ⟨hr12,hm12,hpc12,?_⟩
  change (memoryArgumentsValid s (.LHU .x29 .x19 0)=true ∧ memoryArgumentsValid u1 (.SRLI .x30 .x29 3)=true ∧ memoryArgumentsValid u2 (.ADD .x30 .x30 .x10)=true ∧ memoryArgumentsValid u3 (.LBU .x30 .x30 0)=true ∧ memoryArgumentsValid u4 (.ANDI .x29 .x29 7)=true ∧ memoryArgumentsValid u5 (.SRL .x30 .x30 .x29)=true ∧ memoryArgumentsValid u6 (.ANDI .x30 .x30 1)=true ∧ memoryArgumentsValid u7 (.SLL .x30 .x30 .x28)=true ∧ memoryArgumentsValid u8 (.OR .x6 .x6 .x30)=true ∧ memoryArgumentsValid u9 (.ADDI .x19 .x19 2)=true ∧ memoryArgumentsValid u10 (.ADDI .x28 .x28 1)=true ∧ memoryArgumentsValid u11 (.BNE .x28 .x21 8148)=true ∧ True) ↔ _
  simp only [ha1,ha4, accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_emitByte (s : MachineState) (here : s.pc=pc Block.emitByte.start) :
    (∀ r, (after .emitByte s).getReg r=regOut s r .emitByte) ∧
    (after .emitByte s).mem=(memOut s .emitByte).mem ∧
    (after .emitByte s).pc=pcOut s .emitByte ∧ (Ready s Block.emitByte.ops ↔ accessible s .emitByte) := by
  have hpc0 : s.pc=pc 782 := here
  let u1 := execInstrBr s (.SB .x5 .x6 0)
  have hr1 (r : Reg) : u1.getReg r=s.getReg r := by
    simp only [u1,execInstrBr,MachineState.getReg_setPC,reg_byte,reg_word] <;> rfl
  have hm1 : u1.mem=(s.setByte (s.getReg .x5) ((s.getReg .x6).truncate 8)).mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 783) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have ha1 : (memoryArgumentsValid s (.SB .x5 .x6 0)=true) ↔ (accessValid (s.getReg .x5) 1=true) := by
    simp [memoryArgumentsValid,memAccess,u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc]
  let u2 := execInstrBr u1 (.ADDI .x5 .x5 1)
  have hr2 (r : Reg) : u2.getReg r=if .x5=r then ((s.getReg .x5) + 1#64) else s.getReg r := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hm2 : u2.mem=(s.setByte (s.getReg .x5) ((s.getReg .x6).truncate 8)).mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(pc 784) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  let u3 := execInstrBr u2 (.BNE .x5 .x7 8128)
  have hr3 (r : Reg) : u3.getReg r=if .x5=r then ((s.getReg .x5) + 1#64) else s.getReg r := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hm3 : u3.mem=(s.setByte (s.getReg .x5) ((s.getReg .x6).truncate 8)).mem := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hpc3 : u3.pc=(if ((s.getReg .x5) + 1#64) != (s.getReg .x7) then pc 768 else pc 785) := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  refine ⟨hr3,hm3,hpc3,?_⟩
  change (memoryArgumentsValid s (.SB .x5 .x6 0)=true ∧ memoryArgumentsValid u1 (.ADDI .x5 .x5 1)=true ∧ memoryArgumentsValid u2 (.BNE .x5 .x7 8128)=true ∧ True) ↔ _
  simp only [ha1, accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_ret (s : MachineState) (here : s.pc=pc Block.ret.start) :
    (∀ r, (after .ret s).getReg r=regOut s r .ret) ∧
    (after .ret s).mem=(memOut s .ret).mem ∧
    (after .ret s).pc=pcOut s .ret ∧ (Ready s Block.ret.ops ↔ accessible s .ret) := by
  have hpc0 : s.pc=pc 785 := here
  let u1 := execInstrBr s (.JALR .x0 .x31 0)
  have hr1 (r : Reg) : u1.getReg r=s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(((s.getReg .x31) &&& ~~~1#64)) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  refine ⟨hr1,hm1,hpc1,?_⟩
  change (memoryArgumentsValid s (.JALR .x0 .x31 0)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

end CommitGolfCandidate.Layout2
