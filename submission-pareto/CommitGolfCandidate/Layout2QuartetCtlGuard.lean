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
theorem ctl_guard (s : MachineState) (here : s.pc=pc 1001) :
    ∃ t, Runs checkImage s t 4 7 ∧ t.pc=(if BitVec.ult (s.getReg .x17) (s.getReg .x16*534#64) then pc 364 else pc 790) ∧ t.mem=s.mem ∧
      ∀ r, t.getReg r=(if .x6=r then (s.getReg .x16*534#64) else if .x6=r then (0#64+534#64) else s.getReg r) := by
  obtain ⟨u0,run0,p0,m0,r0⟩:=atom0 s here
  obtain ⟨u1,run1,p1,m1,r1⟩:=atom787 u0 p0
  obtain ⟨u2,run2,p2,m2,r2⟩:=atom788 u1 p1
  obtain ⟨u3,run3,p3,m3,r3⟩:=atom789 u2 p2
  refine ⟨u3,(((run0.thenDo run1).thenDo run2).thenDo run3),?_,(m3.trans (m2.trans (m1.trans m0))),?_⟩
  · simpa [r3,r2,r1,r0,signExtend12,BitVec.add_assoc] using p3
  · intro r;cases r <;> simp [r3,r2,r1,r0,signExtend12,BitVec.add_assoc]

theorem ctl_empty (s : MachineState) (here : s.pc=pc 790) :
    ∃ t, Runs checkImage s t 1 1 ∧ t.pc=(if s.getReg .x16==0#64 then pc 786 else pc 791) ∧ t.mem=s.mem ∧
      ∀ r, t.getReg r=(s.getReg r) := by
  obtain ⟨u0,run0,p0,m0,r0⟩:=atom790 s here
  refine ⟨u0,run0,?_,m0,?_⟩
  · simpa [r0,signExtend12,BitVec.add_assoc] using p0
  · intro r;cases r <;> simp [r0,signExtend12,BitVec.add_assoc]

theorem ctl_init (s : MachineState) (here : s.pc=pc 791) :
    ∃ t, Runs checkImage s t 4 4 ∧ t.pc=(pc 795) ∧ t.mem=s.mem ∧
      ∀ r, t.getReg r=(if .x19=r then (0#64+0#64) else if .x18=r then ((s.getReg .x16)+0#64) else if .x9=r then ((s.getReg .x13)+0#64) else if .x8=r then ((s.getReg .x15)+0#64) else s.getReg r) := by
  obtain ⟨u0,run0,p0,m0,r0⟩:=atom791 s here
  obtain ⟨u1,run1,p1,m1,r1⟩:=atom792 u0 p0
  obtain ⟨u2,run2,p2,m2,r2⟩:=atom793 u1 p1
  obtain ⟨u3,run3,p3,m3,r3⟩:=atom794 u2 p2
  refine ⟨u3,(((run0.thenDo run1).thenDo run2).thenDo run3),?_,(m3.trans (m2.trans (m1.trans m0))),?_⟩
  · simpa [r3,r2,r1,r0,signExtend12,BitVec.add_assoc] using p3
  · intro r;cases r <;> simp [r3,r2,r1,r0,signExtend12,BitVec.add_assoc]

end CommitGolfCandidate.Layout2.Quartet
