import CommitGolfCandidate.TruncGuardEdges
namespace CommitGolfCandidate.Trunc.Guard
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 250000

theorem early (s : MachineState) (pc : s.pc=loc 277) (scratch : s.getReg .x21=256) (lt : ¬(s.getReg .x29+1).toNat<(s.getReg .x30).toNat) :
    Runs (submission.image .check) s ((if false then cleared s else s).setPC (loc 1015)) 10 10 := by
  have h0:=jump s false (s.getReg .x29) 277 994 2868 (by decide) (by rfl) (by decide)
  have h1:=add s false (s.getReg .x29) (s.getReg .x29+1) 994 995 1 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h2:=ge s (s.getReg .x29+1) 995 1008 52 (by decide) (by rfl) (by rw [if_pos lt];decide)
  have h3:=add s false (s.getReg .x29+1) (s.getReg .x29) 1008 1009 4095 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h4:=nop s false (s.getReg .x29) 1009 1010 (by decide) (by rfl) (by decide)
  have h5:=nop s false (s.getReg .x29) 1010 1011 (by decide) (by rfl) (by decide)
  have h6:=nop s false (s.getReg .x29) 1011 1012 (by decide) (by rfl) (by decide)
  have h7:=nop s false (s.getReg .x29) 1012 1013 (by decide) (by rfl) (by decide)
  have h8:=nop s false (s.getReg .x29) 1013 1014 (by decide) (by rfl) (by decide)
  have h9:=jump s false (s.getReg .x29) 1014 1015 4 (by decide) (by rfl) (by decide)
  have h : Runs (submission.image .check) (ghost s false (s.getReg .x29) 277) (ghost s false (s.getReg .x29) 1015) 10 10 := (chain (chain (chain (chain (chain (chain (chain (chain (chain h0 h1) h2) h3) h4) h5) h6) h7) h8) h9)
  rwa [atStart s 277 pc,atEnd] at h

theorem interior (s : MachineState) (pc : s.pc=loc 277) (scratch : s.getReg .x21=256) (lt : (s.getReg .x29+1).toNat<(s.getReg .x30).toNat) (zero : s.getReg .x29-1≠0) :
    Runs (submission.image .check) s ((if true then cleared s else s).setPC (loc 1015)) 10 10 := by
  have h0:=jump s false (s.getReg .x29) 277 994 2868 (by decide) (by rfl) (by decide)
  have h1:=add s false (s.getReg .x29) (s.getReg .x29+1) 994 995 1 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h2:=ge s (s.getReg .x29+1) 995 996 52 (by decide) (by rfl) (by rw [if_neg (not_not_intro lt)];decide)
  have h3:=add s false (s.getReg .x29+1) (s.getReg .x29-1) 996 997 4094 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h4:=nz s (s.getReg .x29-1) 997 1003 24 (by decide) (by rfl) (by rw [if_pos zero];decide)
  have h5:=nop s false (s.getReg .x29-1) 1003 1004 (by decide) (by rfl) (by decide)
  have h6:=mask s scratch (s.getReg .x29-1) 1004 1005 (by decide) (by rfl) (by decide)
  have h7:=jump s true (s.getReg .x29-1) 1005 1006 4 (by decide) (by rfl) (by decide)
  have h8:=add s true (s.getReg .x29-1) (s.getReg .x29) 1006 1007 1 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h9:=jump s true (s.getReg .x29) 1007 1015 32 (by decide) (by rfl) (by decide)
  have h : Runs (submission.image .check) (ghost s false (s.getReg .x29) 277) (ghost s true (s.getReg .x29) 1015) 10 10 := (chain (chain (chain (chain (chain (chain (chain (chain (chain h0 h1) h2) h3) h4) h5) h6) h7) h8) h9)
  rwa [atStart s 277 pc,atEnd] at h

theorem top (s : MachineState) (pc : s.pc=loc 277) (scratch : s.getReg .x21=256) (lt : (s.getReg .x29+1).toNat<(s.getReg .x30).toNat) (zero : s.getReg .x29-1=0) (slot : s.getReg .x19=0) :
    Runs (submission.image .check) s ((if false then cleared s else s).setPC (loc 1015)) 10 10 := by
  have h0:=jump s false (s.getReg .x29) 277 994 2868 (by decide) (by rfl) (by decide)
  have h1:=add s false (s.getReg .x29) (s.getReg .x29+1) 994 995 1 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h2:=ge s (s.getReg .x29+1) 995 996 52 (by decide) (by rfl) (by rw [if_neg (not_not_intro lt)];decide)
  have h3:=add s false (s.getReg .x29+1) (s.getReg .x29-1) 996 997 4094 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h4:=nz s (s.getReg .x29-1) 997 998 24 (by decide) (by rfl) (by rw [if_neg (not_not_intro zero)];decide)
  have h5:=slotZero s (s.getReg .x29-1) 998 1001 12 (by decide) (by rfl) (by rw [if_pos slot];decide)
  have h6:=nop s false (s.getReg .x29-1) 1001 1002 (by decide) (by rfl) (by decide)
  have h7:=jump s false (s.getReg .x29-1) 1002 1006 16 (by decide) (by rfl) (by decide)
  have h8:=add s false (s.getReg .x29-1) (s.getReg .x29) 1006 1007 1 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h9:=jump s false (s.getReg .x29) 1007 1015 32 (by decide) (by rfl) (by decide)
  have h : Runs (submission.image .check) (ghost s false (s.getReg .x29) 277) (ghost s false (s.getReg .x29) 1015) 10 10 := (chain (chain (chain (chain (chain (chain (chain (chain (chain h0 h1) h2) h3) h4) h5) h6) h7) h8) h9)
  rwa [atStart s 277 pc,atEnd] at h

theorem pair (s : MachineState) (pc : s.pc=loc 277) (scratch : s.getReg .x21=256) (lt : (s.getReg .x29+1).toNat<(s.getReg .x30).toNat) (zero : s.getReg .x29-1=0) (slot : s.getReg .x19≠0) :
    Runs (submission.image .check) s ((if true then cleared s else s).setPC (loc 1015)) 10 10 := by
  have h0:=jump s false (s.getReg .x29) 277 994 2868 (by decide) (by rfl) (by decide)
  have h1:=add s false (s.getReg .x29) (s.getReg .x29+1) 994 995 1 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h2:=ge s (s.getReg .x29+1) 995 996 52 (by decide) (by rfl) (by rw [if_neg (not_not_intro lt)];decide)
  have h3:=add s false (s.getReg .x29+1) (s.getReg .x29-1) 996 997 4094 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h4:=nz s (s.getReg .x29-1) 997 998 24 (by decide) (by rfl) (by rw [if_neg (not_not_intro zero)];decide)
  have h5:=slotZero s (s.getReg .x29-1) 998 999 12 (by decide) (by rfl) (by rw [if_neg slot];decide)
  have h6:=mask s scratch (s.getReg .x29-1) 999 1000 (by decide) (by rfl) (by decide)
  have h7:=jump s true (s.getReg .x29-1) 1000 1006 24 (by decide) (by rfl) (by decide)
  have h8:=add s true (s.getReg .x29-1) (s.getReg .x29) 1006 1007 1 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h9:=jump s true (s.getReg .x29) 1007 1015 32 (by decide) (by rfl) (by decide)
  have h : Runs (submission.image .check) (ghost s false (s.getReg .x29) 277) (ghost s true (s.getReg .x29) 1015) 10 10 := (chain (chain (chain (chain (chain (chain (chain (chain (chain h0 h1) h2) h3) h4) h5) h6) h7) h8) h9)
  rwa [atStart s 277 pc,atEnd] at h

theorem runGuard (s : MachineState) (pc : s.pc=loc 277) (scratch : s.getReg .x21=256) :
    Runs (submission.image .check) s ((if guardTest s then cleared s else s).setPC (loc 1015)) 10 10 := by
  by_cases lt : (s.getReg .x29+1).toNat<(s.getReg .x30).toNat
  · by_cases z : s.getReg .x29-1=0
    · by_cases sl : s.getReg .x19=0
      · simpa only [guardTest,lt,z,sl,ne_eq,not_true_eq_false,or_self,and_false,Bool.false_eq_true,ite_false] using top s pc scratch lt z sl
      · rw [if_pos ⟨lt,Or.inr sl⟩];exact pair s pc scratch lt z sl
    · rw [if_pos ⟨lt,Or.inl z⟩];exact interior s pc scratch lt z
  · rw [if_neg (fun h=>lt h.1)];exact early s pc scratch lt

end CommitGolfCandidate.Trunc.Guard
