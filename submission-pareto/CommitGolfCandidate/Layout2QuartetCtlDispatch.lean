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
theorem ctl_dispatch (s : MachineState) (here : s.pc=pc 795) (valid : accessValid (s.getReg .x9) 8=true) :
    ∃ t, Runs checkImage s t 3 3 ∧ t.pc=(if (s.getMem (s.getReg .x9) &&& 3#64)==0#64 then pc 804 else pc 798) ∧ t.mem=s.mem ∧
      ∀ r, t.getReg r=(if .x5=r then (s.getMem (s.getReg .x9) &&& 3#64) else if .x5=r then (s.getMem (s.getReg .x9)) else s.getReg r) := by
  obtain ⟨u0,run0,p0,m0,r0⟩:=atom795 s here valid
  obtain ⟨u1,run1,p1,m1,r1⟩:=atom796 u0 p0
  obtain ⟨u2,run2,p2,m2,r2⟩:=atom797 u1 p1
  refine ⟨u2,((run0.thenDo run1).thenDo run2),?_,(m2.trans (m1.trans m0)),?_⟩
  · simpa [r2,r1,r0,signExtend12,BitVec.add_assoc] using p2
  · intro r;cases r <;> simp [r2,r1,r0,signExtend12,BitVec.add_assoc]

theorem ctl_dec798 (s : MachineState) (here : s.pc=pc 798) :
    ∃ t, Runs checkImage s t 2 2 ∧ t.pc=(if (s.getReg .x5+(signExtend12 4095))==0#64 then pc 851 else pc 800) ∧ t.mem=s.mem ∧
      ∀ r, t.getReg r=(if .x5=r then ((s.getReg .x5)+(signExtend12 4095)) else s.getReg r) := by
  obtain ⟨u0,run0,p0,m0,r0⟩:=atom798 s here
  obtain ⟨u1,run1,p1,m1,r1⟩:=atom799 u0 p0
  refine ⟨u1,(run0.thenDo run1),?_,(m1.trans m0),?_⟩
  · simpa [r1,r0,signExtend12,BitVec.add_assoc] using p1
  · intro r;cases r <;> simp [r1,r0,signExtend12,BitVec.add_assoc]

theorem ctl_dec800 (s : MachineState) (here : s.pc=pc 800) :
    ∃ t, Runs checkImage s t 2 2 ∧ t.pc=(if (s.getReg .x5+(signExtend12 4095))==0#64 then pc 898 else pc 802) ∧ t.mem=s.mem ∧
      ∀ r, t.getReg r=(if .x5=r then ((s.getReg .x5)+(signExtend12 4095)) else s.getReg r) := by
  obtain ⟨u0,run0,p0,m0,r0⟩:=atom800 s here
  obtain ⟨u1,run1,p1,m1,r1⟩:=atom801 u0 p0
  refine ⟨u1,(run0.thenDo run1),?_,(m1.trans m0),?_⟩
  · simpa [r1,r0,signExtend12,BitVec.add_assoc] using p1
  · intro r;cases r <;> simp [r1,r0,signExtend12,BitVec.add_assoc]

theorem ctl_lastQ (s : MachineState) (here : s.pc=pc 802) :
    ∃ t, Runs checkImage s t 2 2 ∧ t.pc=(pc 945) ∧ t.mem=s.mem ∧
      ∀ r, t.getReg r=(if .x5=r then ((s.getReg .x5)+(signExtend12 4095)) else s.getReg r) := by
  obtain ⟨u0,run0,p0,m0,r0⟩:=atom802 s here
  obtain ⟨u1,run1,p1,m1,r1⟩:=atom803 u0 p0
  refine ⟨u1,(run0.thenDo run1),?_,(m1.trans m0),?_⟩
  · simpa [r1,r0,signExtend12,BitVec.add_assoc] using p1
  · intro r;cases r <;> simp [r1,r0,signExtend12,BitVec.add_assoc]

end CommitGolfCandidate.Layout2.Quartet
