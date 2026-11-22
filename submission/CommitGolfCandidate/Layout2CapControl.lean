import CommitGolfCandidate.Layout2CapAtoms
import CommitGolfCandidate.Layout2Clear
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
attribute [local irreducible] execute checkImage
theorem ctl_guard (s : MachineState) (here : s.pc=pc 0) :
    ∃ t, Runs checkImage s t 4 7 ∧ t.pc=(if BitVec.ult (s.getReg .x17) ((s.getReg .x16)*534#64) then pc 364 else pc 1005) ∧ t.mem=s.mem ∧ (∀ r,t.getReg r=(if .x6=r then ((s.getReg .x16)*534#64) else s.getReg r)) ∧ Kept temps s t := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=atom0 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=atom1002 u0 p0
  obtain ⟨u2,h2,p2,m2,r2⟩:=atom1003 u1 p1
  obtain ⟨u3,h3,p3,m3,r3⟩:=atom1004 u2 p2
  refine ⟨u3,(((h0.thenDo h1).thenDo h2).thenDo h3),?_,(m3.trans (m2.trans (m1.trans m0))),?_,?_⟩
  · simpa [r3,r2,r1,r0,signExtend12] using p3
  · intro r;cases r <;> simp [r3,r2,r1,r0,signExtend12]
  · intro r fr;cases r <;> first | exact (fr (by decide)).elim | simp [r3,r2,r1,r0,signExtend12]

theorem ctl_empty (s : MachineState) (here : s.pc=pc 1005) :
    ∃ t, Runs checkImage s t 1 1 ∧ t.pc=(if (s.getReg .x16) == 0#64 then pc 1154 else pc 1006) ∧ t.mem=s.mem ∧ (∀ r,t.getReg r=(s.getReg r)) ∧ Kept temps s t := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=atom1005 s here
  refine ⟨u0,h0,?_,m0,?_,?_⟩
  · simpa [r0,signExtend12] using p0
  · intro r;cases r <;> simp [r0,signExtend12]
  · intro r fr;cases r <;> first | exact (fr (by decide)).elim | simp [r0,signExtend12]

theorem ctl_init (s : MachineState) (here : s.pc=pc 1006) :
    ∃ t, Runs checkImage s t 4 4 ∧ t.pc=(pc 1010) ∧ t.mem=s.mem ∧ (∀ r,t.getReg r=(if .x21=r then 8#64 else if .x20=r then 952#64 else if .x9=r then ((s.getReg .x17)-(s.getReg .x6)) else if .x8=r then ((s.getReg .x15)+(s.getReg .x6)) else s.getReg r)) ∧ Kept temps s t := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=atom1006 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=atom1007 u0 p0
  obtain ⟨u2,h2,p2,m2,r2⟩:=atom1008 u1 p1
  obtain ⟨u3,h3,p3,m3,r3⟩:=atom1009 u2 p2
  refine ⟨u3,(((h0.thenDo h1).thenDo h2).thenDo h3),?_,(m3.trans (m2.trans (m1.trans m0))),?_,?_⟩
  · simpa [r3,r2,r1,r0,signExtend12] using p3
  · intro r;cases r <;> simp [r3,r2,r1,r0,signExtend12]
  · intro r fr;cases r <;> first | exact (fr (by decide)).elim | simp [r3,r2,r1,r0,signExtend12]

theorem ctl_choose (s : MachineState) (here : s.pc=pc 1010) :
    ∃ t, Runs checkImage s t 1 1 ∧ t.pc=(if BitVec.ult (s.getReg .x9) (s.getReg .x20) then pc 1019 else pc 1011) ∧ t.mem=s.mem ∧ (∀ r,t.getReg r=(s.getReg r)) ∧ Kept temps s t := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=atom1010 s here
  refine ⟨u0,h0,?_,m0,?_,?_⟩
  · simpa [r0,signExtend12] using p0
  · intro r;cases r <;> simp [r0,signExtend12]
  · intro r fr;cases r <;> first | exact (fr (by decide)).elim | simp [r0,signExtend12]

theorem ctl_full (s : MachineState) (here : s.pc=pc 1011) :
    ∃ t, Runs checkImage s t 5 5 ∧ t.pc=(pc 759) ∧ t.mem=s.mem ∧ (∀ r,t.getReg r=(if .x31=r then (pc 1016) else if .x19=r then ((86016#64+(signExtend12 3776))+(s.getReg .x2)) else if .x18=r then 952#64 else s.getReg r)) ∧ Kept temps s t := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=atom1011 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=atom1012 u0 p0
  obtain ⟨u2,h2,p2,m2,r2⟩:=atom1013 u1 p1
  obtain ⟨u3,h3,p3,m3,r3⟩:=atom1014 u2 p2
  obtain ⟨u4,h4,p4,m4,r4⟩:=atom1015 u3 p3
  refine ⟨u4,((((h0.thenDo h1).thenDo h2).thenDo h3).thenDo h4),?_,(m4.trans (m3.trans (m2.trans (m1.trans m0)))),?_,?_⟩
  · simpa [r4,r3,r2,r1,r0,signExtend12] using p4
  · intro r;cases r <;> simp [r4,r3,r2,r1,r0,signExtend12]
  · intro r fr;cases r <;> first | exact (fr (by decide)).elim | simp [r4,r3,r2,r1,r0,signExtend12]

theorem ctl_advance (s : MachineState) (here : s.pc=pc 1016) :
    ∃ t, Runs checkImage s t 3 3 ∧ t.pc=(pc 1010) ∧ t.mem=s.mem ∧ (∀ r,t.getReg r=(if .x9=r then ((s.getReg .x9)+(signExtend12 3144)) else if .x8=r then ((s.getReg .x8)+952#64) else s.getReg r)) ∧ Kept temps s t := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=atom1016 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=atom1017 u0 p0
  obtain ⟨u2,h2,p2,m2,r2⟩:=atom1018 u1 p1
  refine ⟨u2,((h0.thenDo h1).thenDo h2),?_,(m2.trans (m1.trans m0)),?_,?_⟩
  · simpa [r2,r1,r0,signExtend12] using p2
  · intro r;cases r <;> simp [r2,r1,r0,signExtend12]
  · intro r fr;cases r <;> first | exact (fr (by decide)).elim | simp [r2,r1,r0,signExtend12]

theorem ctl_locate (s : MachineState) (here : s.pc=pc 1019) :
    ∃ t, Runs checkImage s t 8 11 ∧ t.pc=(pc 1027) ∧ t.mem=s.mem ∧ (∀ r,t.getReg r=(if .x19=r then (((86016#64+(signExtend12 3520))+(s.getReg .x2))+((rv64_divu ((s.getReg .x9)+6#64) 30#64) <<< (3:Nat))) else if .x5=r then ((rv64_divu ((s.getReg .x9)+6#64) 30#64) <<< (3:Nat)) else if .x6=r then 30#64 else s.getReg r)) ∧ Kept temps s t := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=atom1019 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=atom1020 u0 p0
  obtain ⟨u2,h2,p2,m2,r2⟩:=atom1021 u1 p1
  obtain ⟨u3,h3,p3,m3,r3⟩:=atom1022 u2 p2
  obtain ⟨u4,h4,p4,m4,r4⟩:=atom1023 u3 p3
  obtain ⟨u5,h5,p5,m5,r5⟩:=atom1024 u4 p4
  obtain ⟨u6,h6,p6,m6,r6⟩:=atom1025 u5 p5
  obtain ⟨u7,h7,p7,m7,r7⟩:=atom1026 u6 p6
  refine ⟨u7,(((((((h0.thenDo h1).thenDo h2).thenDo h3).thenDo h4).thenDo h5).thenDo h6).thenDo h7),?_,(m7.trans (m6.trans (m5.trans (m4.trans (m3.trans (m2.trans (m1.trans m0))))))),?_,?_⟩
  · simpa [r7,r6,r5,r4,r3,r2,r1,r0,signExtend12] using p7
  · intro r;cases r <;> simp [r7,r6,r5,r4,r3,r2,r1,r0,signExtend12]
  · intro r fr;cases r <;> first | exact (fr (by decide)).elim | simp [r7,r6,r5,r4,r3,r2,r1,r0,signExtend12]

theorem ctl_compare (s : MachineState) (here : s.pc=pc 1027) (valid : accessValid (s.getReg .x19) 2=true) :
    ∃ t, Runs checkImage s t 2 2 ∧ t.pc=(if ((s.getHalfword (s.getReg .x19)).zeroExtend 64) != (s.getReg .x9) then pc 364 else pc 1029) ∧ t.mem=s.mem ∧ (∀ r,t.getReg r=(if .x6=r then ((s.getHalfword (s.getReg .x19)).zeroExtend 64) else s.getReg r)) ∧ Kept temps s t := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=atom1027 s here valid
  obtain ⟨u1,h1,p1,m1,r1⟩:=atom1028 u0 p0
  refine ⟨u1,(h0.thenDo h1),?_,(m1.trans m0),?_,?_⟩
  · simpa [r1,r0,signExtend12] using p1
  · intro r;cases r <;> simp [r1,r0,signExtend12]
  · intro r fr;cases r <;> first | exact (fr (by decide)).elim | simp [r1,r0,signExtend12]

theorem ctl_zeroTail (s : MachineState) (here : s.pc=pc 1029) :
    ∃ t, Runs checkImage s t 1 1 ∧ t.pc=(if (s.getReg .x9) == 0#64 then pc 1034 else pc 1030) ∧ t.mem=s.mem ∧ (∀ r,t.getReg r=(s.getReg r)) ∧ Kept temps s t := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=atom1029 s here
  refine ⟨u0,h0,?_,m0,?_,?_⟩
  · simpa [r0,signExtend12] using p0
  · intro r;cases r <;> simp [r0,signExtend12]
  · intro r fr;cases r <;> first | exact (fr (by decide)).elim | simp [r0,signExtend12]

theorem ctl_partial (s : MachineState) (here : s.pc=pc 1030) (valid : accessValid ((s.getReg .x19)+4#64) 4=true) :
    ∃ t, Runs checkImage s t 4 4 ∧ t.pc=(pc 759) ∧ t.mem=s.mem ∧ (∀ r,t.getReg r=(if .x31=r then (pc 1034) else if .x18=r then (s.getReg .x9) else if .x19=r then ((s.getReg .x2)+((s.getWord32 ((s.getReg .x19)+4#64)).zeroExtend 64)) else if .x6=r then ((s.getWord32 ((s.getReg .x19)+4#64)).zeroExtend 64) else s.getReg r)) ∧ Kept temps s t := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=atom1030 s here valid
  obtain ⟨u1,h1,p1,m1,r1⟩:=atom1031 u0 p0
  obtain ⟨u2,h2,p2,m2,r2⟩:=atom1032 u1 p1
  obtain ⟨u3,h3,p3,m3,r3⟩:=atom1033 u2 p2
  refine ⟨u3,(((h0.thenDo h1).thenDo h2).thenDo h3),?_,(m3.trans (m2.trans (m1.trans m0))),?_,?_⟩
  · simpa [r3,r2,r1,r0,signExtend12] using p3
  · intro r;cases r <;> simp [r3,r2,r1,r0,signExtend12]
  · intro r fr;cases r <;> first | exact (fr (by decide)).elim | simp [r3,r2,r1,r0,signExtend12]

theorem ctl_clearExit (s : MachineState) (here : s.pc=pc 1153) :
    ∃ t, Runs checkImage s t 1 1 ∧ t.pc=(pc 1001) ∧ t.mem=s.mem ∧ (∀ r,t.getReg r=(s.getReg r)) ∧ Kept temps s t := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=atom1153 s here
  refine ⟨u0,h0,?_,m0,?_,?_⟩
  · simpa [r0,signExtend12] using p0
  · intro r;cases r <;> simp [r0,signExtend12]
  · intro r fr;cases r <;> first | exact (fr (by decide)).elim | simp [r0,signExtend12]

theorem ctl_emptyLen (s : MachineState) (here : s.pc=pc 1154) :
    ∃ t, Runs checkImage s t 1 1 ∧ t.pc=(if (s.getReg .x17) != 0#64 then pc 364 else pc 1155) ∧ t.mem=s.mem ∧ (∀ r,t.getReg r=(s.getReg r)) ∧ Kept temps s t := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=atom1154 s here
  refine ⟨u0,h0,?_,m0,?_,?_⟩
  · simpa [r0,signExtend12] using p0
  · intro r;cases r <;> simp [r0,signExtend12]
  · intro r fr;cases r <;> first | exact (fr (by decide)).elim | simp [r0,signExtend12]

theorem ctl_emptyExit (s : MachineState) (here : s.pc=pc 1155) :
    ∃ t, Runs checkImage s t 1 1 ∧ t.pc=(pc 1001) ∧ t.mem=s.mem ∧ (∀ r,t.getReg r=(s.getReg r)) ∧ Kept temps s t := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=atom1155 s here
  refine ⟨u0,h0,?_,m0,?_,?_⟩
  · simpa [r0,signExtend12] using p0
  · intro r;cases r <;> simp [r0,signExtend12]
  · intro r fr;cases r <;> first | exact (fr (by decide)).elim | simp [r0,signExtend12]

end CommitGolfCandidate.Layout2.Cap
