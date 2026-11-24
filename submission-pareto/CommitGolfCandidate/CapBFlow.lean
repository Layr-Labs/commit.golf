import CommitGolfCandidate.CapBFlowAtoms
namespace CommitGolfCandidate.CapB
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.GroupedOpening (openingImage)
open TwoPermutationPrototype.Opening (getReg_setReg getReg_setMem)
set_option maxRecDepth 12000
set_option maxHeartbeats 1100000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
theorem nav_visit (s : MachineState) (here : s.pc=pc 661) (valid : accessValid ((s.getReg .x26)+((s.getReg .x6) <<< (3:Nat))) 8=true) :
    ∃ t, Run openingImage s t 4 4 ∧ t.pc=(if (s.getMem ((s.getReg .x26)+((s.getReg .x6) <<< (3:Nat)))) == 0#64 then pc 702 else pc 665) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x28=r then (s.getMem ((s.getReg .x26)+((s.getReg .x6) <<< (3:Nat)))) else if .x7=r then ((s.getReg .x26)+((s.getReg .x6) <<< (3:Nat))) else if .x16=r then ((s.getReg .x6) <<< (3:Nat)) else s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf661 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=leaf662 u0 p0
  obtain ⟨u2,h2,p2,m2,r2⟩:=leaf663 u1 p1 (by simpa [r1,r0,BitVec.add_assoc] using valid)
  obtain ⟨u3,h3,p3,m3,r3⟩:=leaf664 u2 p2
  refine ⟨u3,(((h0.thenDo h1).thenDo h2).thenDo h3),?_,(m3.trans (m2.trans (m1.trans m0))),?_⟩
  · simpa [r3,r2,r1,r0,m3,m2,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p3
  · intro r;cases r <;> simp [r3,r2,r1,r0,m3,m2,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_level (s : MachineState) (here : s.pc=pc 665) :
    ∃ t, Run openingImage s t 1 1 ∧ t.pc=(if !(BitVec.ult (s.getReg .x16) (s.getReg .x27)) then pc 668 else pc 666) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf665 s here
  refine ⟨u0,h0,?_,m0,?_⟩
  · simpa [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p0
  · intro r;cases r <;> simp [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_descend (s : MachineState) (here : s.pc=pc 666) :
    ∃ t, Run openingImage s t 2 2 ∧ t.pc=(pc 661) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x6=r then ((s.getReg .x6) <<< (1:Nat)) else s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf666 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=leaf667 u0 p0
  refine ⟨u1,(h0.thenDo h1),?_,(m1.trans m0),?_⟩
  · simpa [r1,r0,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p1
  · intro r;cases r <;> simp [r1,r0,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_dispatch (s : MachineState) (here : s.pc=pc 668) :
    ∃ t, Run openingImage s t 4 4 ∧ t.pc=(((36864#64+((s.getReg .x28) <<< (6:Nat)))+128#64) &&& ~~~1#64) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x11=r then (36864#64+((s.getReg .x28) <<< (6:Nat))) else if .x28=r then ((s.getReg .x28) <<< (6:Nat)) else s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf668 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=leaf669 u0 p0
  obtain ⟨u2,h2,p2,m2,r2⟩:=leaf670 u1 p1
  obtain ⟨u3,h3,p3,m3,r3⟩:=leaf671 u2 p2
  refine ⟨u3,(((h0.thenDo h1).thenDo h2).thenDo h3),?_,(m3.trans (m2.trans (m1.trans m0))),?_⟩
  · simpa [r3,r2,r1,r0,m3,m2,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p3
  · intro r;cases r <;> simp [r3,r2,r1,r0,m3,m2,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_parity (s : MachineState) (here : s.pc=pc 703) :
    ∃ t, Run openingImage s t 2 2 ∧ t.pc=(if ((s.getReg .x6) &&& 1#64) == 0#64 then pc 660 else pc 705) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x7=r then ((s.getReg .x6) &&& 1#64) else s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf703 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=leaf704 u0 p0
  refine ⟨u1,(h0.thenDo h1),?_,(m1.trans m0),?_⟩
  · simpa [r1,r0,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p1
  · intro r;cases r <;> simp [r1,r0,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_right (s : MachineState) (here : s.pc=pc 660) :
    ∃ t, Run openingImage s t 1 1 ∧ t.pc=(pc 661) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x6=r then ((s.getReg .x6)+1#64) else s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf660 s here
  refine ⟨u0,h0,?_,m0,?_⟩
  · simpa [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p0
  · intro r;cases r <;> simp [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_climb (s : MachineState) (here : s.pc=pc 705) :
    ∃ t, Run openingImage s t 2 2 ∧ t.pc=(if ((s.getReg .x6) >>> (1:Nat)) != (s.getReg .x23) then pc 703 else pc 707) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x6=r then ((s.getReg .x6) >>> (1:Nat)) else s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf705 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=leaf706 u0 p0
  refine ⟨u1,(h0.thenDo h1),?_,(m1.trans m0),?_⟩
  · simpa [r1,r0,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p1
  · intro r;cases r <;> simp [r1,r0,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_finishJump (s : MachineState) (here : s.pc=pc 707) :
    ∃ t, Run openingImage s t 1 1 ∧ t.pc=(pc 6656) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf707 s here
  refine ⟨u0,h0,?_,m0,?_⟩
  · simpa [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p0
  · intro r;cases r <;> simp [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_init (s : MachineState) (here : s.pc=pc 7155) :
    ∃ t, Run openingImage s t 5 5 ∧ t.pc=(if ((s.getReg .x21) &&& 7#64) == 0#64 then pc 7162 else pc 7160) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x14=r then ((s.getReg .x21) &&& 7#64) else if .x24=r then 28672#64 else if .x19=r then 28672#64 else if .x6=r then 1#64 else s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf7155 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=leaf7156 u0 p0
  obtain ⟨u2,h2,p2,m2,r2⟩:=leaf7157 u1 p1
  obtain ⟨u3,h3,p3,m3,r3⟩:=leaf7158 u2 p2
  obtain ⟨u4,h4,p4,m4,r4⟩:=leaf7159 u3 p3
  refine ⟨u4,((((h0.thenDo h1).thenDo h2).thenDo h3).thenDo h4),?_,(m4.trans (m3.trans (m2.trans (m1.trans m0)))),?_⟩
  · simpa [r4,r3,r2,r1,r0,m4,m3,m2,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p4
  · intro r;cases r <;> simp [r4,r3,r2,r1,r0,m4,m3,m2,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_useScratch (s : MachineState) (here : s.pc=pc 7160) :
    ∃ t, Run openingImage s t 2 2 ∧ t.pc=(pc 7162) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x21=r then 12288#64 else if .x14=r then (s.getReg .x21) else s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf7160 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=leaf7161 u0 p0
  refine ⟨u1,(h0.thenDo h1),?_,(m1.trans m0),?_⟩
  · simpa [r1,r0,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p1
  · intro r;cases r <;> simp [r1,r0,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_enter (s : MachineState) (here : s.pc=pc 7162) :
    ∃ t, Run openingImage s t 1 1 ∧ t.pc=(pc 661) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf7162 s here
  refine ⟨u0,h0,?_,m0,?_⟩
  · simpa [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p0
  · intro r;cases r <;> simp [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_flushTest (s : MachineState) (here : s.pc=pc 6656) :
    ∃ t, Run openingImage s t 1 1 ∧ t.pc=(if (s.getReg .x19) == (s.getReg .x24) then pc 6662 else pc 6657) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf6656 s here
  refine ⟨u0,h0,?_,m0,?_⟩
  · simpa [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p0
  · intro r;cases r <;> simp [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_flushJump (s : MachineState) (here : s.pc=pc 6657) :
    ∃ t, Run openingImage s t 5 5 ∧ t.pc=(((32768#64+(((s.getReg .x19)-(s.getReg .x24)) >>> (1:Nat)))+(signExtend12 2144)) &&& ~~~1#64) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x7=r then (32768#64+(((s.getReg .x19)-(s.getReg .x24)) >>> (1:Nat))) else if .x6=r then (((s.getReg .x19)-(s.getReg .x24)) >>> (1:Nat)) else s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf6657 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=leaf6658 u0 p0
  obtain ⟨u2,h2,p2,m2,r2⟩:=leaf6659 u1 p1
  obtain ⟨u3,h3,p3,m3,r3⟩:=leaf6660 u2 p2
  obtain ⟨u4,h4,p4,m4,r4⟩:=leaf6661 u3 p3
  refine ⟨u4,((((h0.thenDo h1).thenDo h2).thenDo h3).thenDo h4),?_,(m4.trans (m3.trans (m2.trans (m1.trans m0)))),?_⟩
  · simpa [r4,r3,r2,r1,r0,m4,m3,m2,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p4
  · intro r;cases r <;> simp [r4,r3,r2,r1,r0,m4,m3,m2,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_copyTest (s : MachineState) (here : s.pc=pc 6662) :
    ∃ t, Run openingImage s t 1 1 ∧ t.pc=(if (s.getReg .x14) == 0#64 then pc 6671 else pc 6663) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf6662 s here
  refine ⟨u0,h0,?_,m0,?_⟩
  · simpa [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p0
  · intro r;cases r <;> simp [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_copyStart (s : MachineState) (here : s.pc=pc 6663) :
    ∃ t, Run openingImage s t 2 2 ∧ t.pc=(if 12288#64 == (s.getReg .x21) then pc 6670 else pc 6665) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x6=r then 12288#64 else s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf6663 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=leaf6664 u0 p0
  refine ⟨u1,(h0.thenDo h1),?_,(m1.trans m0),?_⟩
  · simpa [r1,r0,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p1
  · intro r;cases r <;> simp [r1,r0,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_copyRead (s : MachineState) (here : s.pc=pc 6665) (valid : accessValid (s.getReg .x6) 1=true) :
    ∃ t, Run openingImage s t 1 1 ∧ t.pc=(pc 6666) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x7=r then ((s.getByte (s.getReg .x6)).zeroExtend 64) else s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf6665 s here valid
  refine ⟨u0,h0,?_,m0,?_⟩
  · simpa [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p0
  · intro r;cases r <;> simp [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_copyWrite (s : MachineState) (here : s.pc=pc 6666) (valid : accessValid (s.getReg .x14) 1=true) :
    ∃ t, Run openingImage s t 1 1 ∧ t.pc=(pc 6667) ∧ t.mem=(s.setByte (s.getReg .x14) ((s.getReg .x7).truncate 8)).mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf6666 s here valid
  refine ⟨u0,h0,?_,m0,?_⟩
  · simpa [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p0
  · intro r;cases r <;> simp [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_copyNext (s : MachineState) (here : s.pc=pc 6667) :
    ∃ t, Run openingImage s t 3 3 ∧ t.pc=(if ((s.getReg .x6)+1#64) != (s.getReg .x21) then pc 6665 else pc 6670) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x14=r then ((s.getReg .x14)+1#64) else if .x6=r then ((s.getReg .x6)+1#64) else s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf6667 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=leaf6668 u0 p0
  obtain ⟨u2,h2,p2,m2,r2⟩:=leaf6669 u1 p1
  refine ⟨u2,((h0.thenDo h1).thenDo h2),?_,(m2.trans (m1.trans m0)),?_⟩
  · simpa [r2,r1,r0,m2,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p2
  · intro r;cases r <;> simp [r2,r1,r0,m2,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_copyDone (s : MachineState) (here : s.pc=pc 6670) :
    ∃ t, Run openingImage s t 1 1 ∧ t.pc=(pc 6671) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x21=r then (s.getReg .x14) else s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf6670 s here
  refine ⟨u0,h0,?_,m0,?_⟩
  · simpa [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p0
  · intro r;cases r <;> simp [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_haltJump (s : MachineState) (here : s.pc=pc 6671) :
    ∃ t, Run openingImage s t 1 1 ∧ t.pc=(pc 709) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf6671 s here
  refine ⟨u0,h0,?_,m0,?_⟩
  · simpa [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p0
  · intro r;cases r <;> simp [r0,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

theorem nav_exit (s : MachineState) (here : s.pc=pc 709) :
    ∃ t, Run openingImage s t 3 3 ∧ t.pc=(pc 712) ∧ t.mem=s.mem ∧ ∀ r,t.getReg r=(if .x10=r then 0#64 else if .x5=r then 1#64 else if .x11=r then ((s.getReg .x21)-(s.getReg .x20)) else s.getReg r) := by
  obtain ⟨u0,h0,p0,m0,r0⟩:=leaf709 s here
  obtain ⟨u1,h1,p1,m1,r1⟩:=leaf710 u0 p0
  obtain ⟨u2,h2,p2,m2,r2⟩:=leaf711 u1 p1
  refine ⟨u2,((h0.thenDo h1).thenDo h2),?_,(m2.trans (m1.trans m0)),?_⟩
  · simpa [r2,r1,r0,m2,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12] using p2
  · intro r;cases r <;> simp [r2,r1,r0,m2,m1,m0,MachineState.getMem,BitVec.add_assoc,signExtend12]

end CommitGolfCandidate.CapB
