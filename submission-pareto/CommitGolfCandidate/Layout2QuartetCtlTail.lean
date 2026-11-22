import CommitGolfCandidate.Layout2QuartetAtoms
import CommitGolfCandidate.Layout2Views

namespace CommitGolfCandidate.Layout2.Quartet
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Opening (getReg_setReg)
set_option maxRecDepth 8000
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
attribute [local simp] zero mem_pc pc_pc mem_reg pc_ite reg_ite mem_ite
attribute [local irreducible] execute checkImage
theorem ctl_jump0 (s : MachineState) (here : s.pc=pc 850) :
    ∃ t, Runs checkImage s t 1 1 ∧ t.pc=(pc 992) ∧ t.mem=s.mem ∧
      ∀ r, t.getReg r=(s.getReg r) := by
  obtain ⟨u0,run0,p0,m0,r0⟩:=atom850 s here
  refine ⟨u0,run0,?_,m0,?_⟩
  · simpa [r0,signExtend12,BitVec.add_assoc] using p0
  · intro r;cases r <;> simp [r0,signExtend12,BitVec.add_assoc]

theorem ctl_jump1 (s : MachineState) (here : s.pc=pc 897) :
    ∃ t, Runs checkImage s t 1 1 ∧ t.pc=(pc 992) ∧ t.mem=s.mem ∧
      ∀ r, t.getReg r=(s.getReg r) := by
  obtain ⟨u0,run0,p0,m0,r0⟩:=atom897 s here
  refine ⟨u0,run0,?_,m0,?_⟩
  · simpa [r0,signExtend12,BitVec.add_assoc] using p0
  · intro r;cases r <;> simp [r0,signExtend12,BitVec.add_assoc]

theorem ctl_jump2 (s : MachineState) (here : s.pc=pc 944) :
    ∃ t, Runs checkImage s t 1 1 ∧ t.pc=(pc 992) ∧ t.mem=s.mem ∧
      ∀ r, t.getReg r=(s.getReg r) := by
  obtain ⟨u0,run0,p0,m0,r0⟩:=atom944 s here
  refine ⟨u0,run0,?_,m0,?_⟩
  · simpa [r0,signExtend12,BitVec.add_assoc] using p0
  · intro r;cases r <;> simp [r0,signExtend12,BitVec.add_assoc]

theorem ctl_jump3 (s : MachineState) (here : s.pc=pc 991) :
    ∃ t, Runs checkImage s t 1 1 ∧ t.pc=(pc 992) ∧ t.mem=s.mem ∧
      ∀ r, t.getReg r=(s.getReg r) := by
  obtain ⟨u0,run0,p0,m0,r0⟩:=atom991 s here
  refine ⟨u0,run0,?_,m0,?_⟩
  · simpa [r0,signExtend12,BitVec.add_assoc] using p0
  · intro r;cases r <;> simp [r0,signExtend12,BitVec.add_assoc]

theorem ctl_tail (s : MachineState) (here : s.pc=pc 992) :
    ∃ t, Runs checkImage s t 2 2 ∧ t.pc=(if (s.getReg .x18+(signExtend12 4095))==0#64 then pc 786 else pc 994) ∧ t.mem=s.mem ∧
      ∀ r, t.getReg r=(if .x18=r then ((s.getReg .x18)+(signExtend12 4095)) else s.getReg r) := by
  obtain ⟨u0,run0,p0,m0,r0⟩:=atom992 s here
  obtain ⟨u1,run1,p1,m1,r1⟩:=atom993 u0 p0
  refine ⟨u1,(run0.thenDo run1),?_,(m1.trans m0),?_⟩
  · simpa [r1,r0,signExtend12,BitVec.add_assoc] using p1
  · intro r;cases r <;> simp [r1,r0,signExtend12,BitVec.add_assoc]

theorem ctl_bump (s : MachineState) (here : s.pc=pc 994) :
    ∃ t, Runs checkImage s t 3 3 ∧ t.pc=(if s.getReg .x19 !=0#64 then pc 998 else pc 997) ∧ t.mem=s.mem ∧
      ∀ r, t.getReg r=(if .x8=r then ((s.getReg .x8)+536#64) else if .x9=r then ((s.getReg .x9)+8#64) else s.getReg r) := by
  obtain ⟨u0,run0,p0,m0,r0⟩:=atom994 s here
  obtain ⟨u1,run1,p1,m1,r1⟩:=atom995 u0 p0
  obtain ⟨u2,run2,p2,m2,r2⟩:=atom996 u1 p1
  refine ⟨u2,((run0.thenDo run1).thenDo run2),?_,(m2.trans (m1.trans m0)),?_⟩
  · simpa [r2,r1,r0,signExtend12,BitVec.add_assoc] using p2
  · intro r;cases r <;> simp [r2,r1,r0,signExtend12,BitVec.add_assoc]

theorem ctl_shortStride (s : MachineState) (here : s.pc=pc 997) :
    ∃ t, Runs checkImage s t 1 1 ∧ t.pc=(pc 998) ∧ t.mem=s.mem ∧
      ∀ r, t.getReg r=(if .x8=r then ((s.getReg .x8)+(signExtend12 4088)) else s.getReg r) := by
  obtain ⟨u0,run0,p0,m0,r0⟩:=atom997 s here
  refine ⟨u0,run0,?_,m0,?_⟩
  · simpa [r0,signExtend12,BitVec.add_assoc] using p0
  · intro r;cases r <;> simp [r0,signExtend12,BitVec.add_assoc]

theorem ctl_next (s : MachineState) (here : s.pc=pc 998) :
    ∃ t, Runs checkImage s t 3 3 ∧ t.pc=(pc 795) ∧ t.mem=s.mem ∧
      ∀ r, t.getReg r=(if .x19=r then ((s.getReg .x19+1#64) &&& 3#64) else if .x19=r then ((s.getReg .x19)+1#64) else s.getReg r) := by
  obtain ⟨u0,run0,p0,m0,r0⟩:=atom998 s here
  obtain ⟨u1,run1,p1,m1,r1⟩:=atom999 u0 p0
  obtain ⟨u2,run2,p2,m2,r2⟩:=atom1000 u1 p1
  refine ⟨u2,((run0.thenDo run1).thenDo run2),?_,(m2.trans (m1.trans m0)),?_⟩
  · simpa [r2,r1,r0,signExtend12,BitVec.add_assoc] using p2
  · intro r;cases r <;> simp [r2,r1,r0,signExtend12,BitVec.add_assoc]

end CommitGolfCandidate.Layout2.Quartet
