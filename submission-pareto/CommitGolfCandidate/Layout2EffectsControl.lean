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
theorem effects_entry (s : MachineState) (here : s.pc=pc Block.entry.start) :
    (∀ r, (after .entry s).getReg r=regOut s r .entry) ∧
    (after .entry s).mem=(memOut s .entry).mem ∧
    (after .entry s).pc=pcOut s .entry ∧ (Ready s Block.entry.ops ↔ accessible s .entry) := by
  have hpc0 : s.pc=pc 0 := here
  let u1 := execInstrBr s (.JAL .x0 2820)
  have hr1 (r : Reg) : u1.getReg r=s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 705) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  refine ⟨hr1,hm1,hpc1,?_⟩
  change (memoryArgumentsValid s (.JAL .x0 2820)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_guard (s : MachineState) (here : s.pc=pc Block.guard.start) :
    (∀ r, (after .guard s).getReg r=regOut s r .guard) ∧
    (after .guard s).mem=(memOut s .guard).mem ∧
    (after .guard s).pc=pcOut s .guard ∧ (Ready s Block.guard.ops ↔ accessible s .guard) := by
  have hpc0 : s.pc=pc 705 := here
  let u1 := execInstrBr s (.ADDI .x6 .x0 534)
  have hr1 (r : Reg) : u1.getReg r=if .x6=r then 534#64 else s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 706) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  let u2 := execInstrBr u1 (.MUL .x6 .x16 .x6)
  have hr2 (r : Reg) : u2.getReg r=if .x6=r then ((s.getReg .x16) * 534#64) else s.getReg r := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hm2 : u2.mem=s.mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(pc 707) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  let u3 := execInstrBr u2 (.BLTU .x17 .x6 6820)
  have hr3 (r : Reg) : u3.getReg r=if .x6=r then ((s.getReg .x16) * 534#64) else s.getReg r := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hm3 : u3.mem=s.mem := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hpc3 : u3.pc=(if BitVec.ult (s.getReg .x17) ((s.getReg .x16) * 534#64) then pc 364 else pc 708) := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  refine ⟨hr3,hm3,hpc3,?_⟩
  change (memoryArgumentsValid s (.ADDI .x6 .x0 534)=true ∧ memoryArgumentsValid u1 (.MUL .x6 .x16 .x6)=true ∧ memoryArgumentsValid u2 (.BLTU .x17 .x6 6820)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_empty (s : MachineState) (here : s.pc=pc Block.empty.start) :
    (∀ r, (after .empty s).getReg r=regOut s r .empty) ∧
    (after .empty s).mem=(memOut s .empty).mem ∧
    (after .empty s).pc=pcOut s .empty ∧ (Ready s Block.empty.ops ↔ accessible s .empty) := by
  have hpc0 : s.pc=pc 708 := here
  let u1 := execInstrBr s (.BEQ .x16 .x0 148)
  have hr1 (r : Reg) : u1.getReg r=s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(if (s.getReg .x16) == 0#64 then pc 745 else pc 709) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  refine ⟨hr1,hm1,hpc1,?_⟩
  change (memoryArgumentsValid s (.BEQ .x16 .x0 148)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_init (s : MachineState) (here : s.pc=pc Block.init.start) :
    (∀ r, (after .init s).getReg r=regOut s r .init) ∧
    (after .init s).mem=(memOut s .init).mem ∧
    (after .init s).pc=pcOut s .init ∧ (Ready s Block.init.ops ↔ accessible s .init) := by
  have hpc0 : s.pc=pc 709 := here
  let u1 := execInstrBr s (.ADDI .x8 .x15 0)
  have hr1 (r : Reg) : u1.getReg r=if .x8=r then (s.getReg .x15) else s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 710) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  let u2 := execInstrBr u1 (.ADDI .x9 .x16 0)
  have hr2 (r : Reg) : u2.getReg r=if .x9=r then (s.getReg .x16) else if .x8=r then (s.getReg .x15) else s.getReg r := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hm2 : u2.mem=s.mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(pc 711) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  let u3 := execInstrBr u2 (.ADDI .x20 .x0 4)
  have hr3 (r : Reg) : u3.getReg r=if .x20=r then 4#64 else if .x9=r then (s.getReg .x16) else if .x8=r then (s.getReg .x15) else s.getReg r := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hm3 : u3.mem=s.mem := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hpc3 : u3.pc=(pc 712) := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  let u4 := execInstrBr u3 (.ADDI .x21 .x0 8)
  have hr4 (r : Reg) : u4.getReg r=if .x21=r then 8#64 else if .x20=r then 4#64 else if .x9=r then (s.getReg .x16) else if .x8=r then (s.getReg .x15) else s.getReg r := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  have hm4 : u4.mem=s.mem := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  have hpc4 : u4.pc=(pc 713) := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  refine ⟨hr4,hm4,hpc4,?_⟩
  change (memoryArgumentsValid s (.ADDI .x8 .x15 0)=true ∧ memoryArgumentsValid u1 (.ADDI .x9 .x16 0)=true ∧ memoryArgumentsValid u2 (.ADDI .x20 .x0 4)=true ∧ memoryArgumentsValid u3 (.ADDI .x21 .x0 8)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_choose (s : MachineState) (here : s.pc=pc Block.choose.start) :
    (∀ r, (after .choose s).getReg r=regOut s r .choose) ∧
    (after .choose s).mem=(memOut s .choose).mem ∧
    (after .choose s).pc=pcOut s .choose ∧ (Ready s Block.choose.ops ↔ accessible s .choose) := by
  have hpc0 : s.pc=pc 713 := here
  let u1 := execInstrBr s (.BLTU .x9 .x20 32)
  have hr1 (r : Reg) : u1.getReg r=s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(if BitVec.ult (s.getReg .x9) (s.getReg .x20) then pc 721 else pc 714) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  refine ⟨hr1,hm1,hpc1,?_⟩
  change (memoryArgumentsValid s (.BLTU .x9 .x20 32)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_full (s : MachineState) (here : s.pc=pc Block.full.start) :
    (∀ r, (after .full s).getReg r=regOut s r .full) ∧
    (after .full s).mem=(memOut s .full).mem ∧
    (after .full s).pc=pcOut s .full ∧ (Ready s Block.full.ops ↔ accessible s .full) := by
  have hpc0 : s.pc=pc 714 := here
  let u1 := execInstrBr s (.ADDI .x18 .x0 2047)
  have hr1 (r : Reg) : u1.getReg r=if .x18=r then 2047#64 else s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(pc 715) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  let u2 := execInstrBr u1 (.ADDI .x18 .x18 89)
  have hr2 (r : Reg) : u2.getReg r=if .x18=r then (2047#64 + 89#64) else s.getReg r := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hm2 : u2.mem=s.mem := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  have hpc2 : u2.pc=(pc 716) := by
    simp +contextual [u2,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr1,hm1,hpc1,BitVec.add_assoc] <;> try rfl
  let u3 := execInstrBr u2 (.ADDI .x19 .x2 0)
  have hr3 (r : Reg) : u3.getReg r=if .x19=r then (s.getReg .x2) else if .x18=r then (2047#64 + 89#64) else s.getReg r := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hm3 : u3.mem=s.mem := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  have hpc3 : u3.pc=(pc 717) := by
    simp +contextual [u3,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr2,hm2,hpc2,BitVec.add_assoc] <;> try rfl
  let u4 := execInstrBr u3 (.JAL .x31 168)
  have hr4 (r : Reg) : u4.getReg r=if .x31=r then (pc 718) else if .x19=r then (s.getReg .x2) else if .x18=r then (2047#64 + 89#64) else s.getReg r := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  have hm4 : u4.mem=s.mem := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  have hpc4 : u4.pc=(pc 759) := by
    simp +contextual [u4,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hr3,hm3,hpc3,BitVec.add_assoc] <;> try rfl
  refine ⟨hr4,hm4,hpc4,?_⟩
  change (memoryArgumentsValid s (.ADDI .x18 .x0 2047)=true ∧ memoryArgumentsValid u1 (.ADDI .x18 .x18 89)=true ∧ memoryArgumentsValid u2 (.ADDI .x19 .x2 0)=true ∧ memoryArgumentsValid u3 (.JAL .x31 168)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

theorem effects_next (s : MachineState) (here : s.pc=pc Block.next.start) :
    (∀ r, (after .next s).getReg r=regOut s r .next) ∧
    (after .next s).mem=(memOut s .next).mem ∧
    (after .next s).pc=pcOut s .next ∧ (Ready s Block.next.ops ↔ accessible s .next) := by
  refine ⟨?_,rfl,?_,?_⟩
  · intro r;cases r <;> rfl
  · change s.pc+4+4+signExtend21 2097124=pc 713
    rw [here];rfl
  · exact ⟨fun _=>trivial, fun _=>⟨rfl,rfl,rfl,trivial⟩⟩

theorem effects_tail (s : MachineState) (here : s.pc=pc Block.tail.start) :
    (∀ r, (after .tail s).getReg r=regOut s r .tail) ∧
    (after .tail s).mem=(memOut s .tail).mem ∧
    (after .tail s).pc=pcOut s .tail ∧ (Ready s Block.tail.ops ↔ accessible s .tail) := by
  have hpc0 : s.pc=pc 721 := here
  let u1 := execInstrBr s (.BEQ .x9 .x0 72)
  have hr1 (r : Reg) : u1.getReg r=s.getReg r := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hm1 : u1.mem=s.mem := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  have hpc1 : u1.pc=(if (s.getReg .x9) == 0#64 then pc 739 else pc 722) := by
    simp +contextual [u1,execInstrBr,getReg_setReg,MachineState.getByte,MachineState.getHalfword,MachineState.getMem,MachineState.setByte,MachineState.setMem,signExtend12,signExtend13,signExtend21,pc,hpc0,BitVec.add_assoc] <;> try rfl
  refine ⟨hr1,hm1,hpc1,?_⟩
  change (memoryArgumentsValid s (.BEQ .x9 .x0 72)=true ∧ True) ↔ _
  simp only [accessible,true_and,and_true] <;> simp [memoryArgumentsValid,memAccess]

end CommitGolfCandidate.Layout2
