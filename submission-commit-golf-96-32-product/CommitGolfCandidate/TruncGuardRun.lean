import CommitGolfCandidate.TruncGuardEdges
namespace CommitGolfCandidate.Trunc.Guard
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
set_option maxHeartbeats 250000

theorem early (s : MachineState) (pc : s.pc=loc 252) (scratch : s.getReg .x21=256) (lt : ¬(s.getReg .x29+1).toNat<(s.getReg .x30).toNat) :
    Runs (Trunc.wireImage true) s ((if false then cleared s else s).setPC (loc 1047)) 10 10 := by
  have h0:=jump s false (s.getReg .x29) 252 1026 3096 (by decide) (by rfl) (by decide)
  have h1:=add s false (s.getReg .x29) (s.getReg .x29+1) 1026 1027 1 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h2:=ge s (s.getReg .x29+1) 1027 1040 52 (by decide) (by rfl) (by rw [if_pos lt];decide)
  have h3:=add s false (s.getReg .x29+1) (s.getReg .x29) 1040 1041 4095 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h4:=nop s false (s.getReg .x29) 1041 1042 (by decide) (by rfl) (by decide)
  have h5:=nop s false (s.getReg .x29) 1042 1043 (by decide) (by rfl) (by decide)
  have h6:=nop s false (s.getReg .x29) 1043 1044 (by decide) (by rfl) (by decide)
  have h7:=nop s false (s.getReg .x29) 1044 1045 (by decide) (by rfl) (by decide)
  have h8:=nop s false (s.getReg .x29) 1045 1046 (by decide) (by rfl) (by decide)
  have h9:=jump s false (s.getReg .x29) 1046 1047 4 (by decide) (by rfl) (by decide)
  have h : Runs (Trunc.wireImage true) (ghost s false (s.getReg .x29) 252) (ghost s false (s.getReg .x29) 1047) 10 10 := (chain (chain (chain (chain (chain (chain (chain (chain (chain h0 h1) h2) h3) h4) h5) h6) h7) h8) h9)
  rwa [atStart s 252 pc,atEnd] at h

theorem interior (s : MachineState) (pc : s.pc=loc 252) (scratch : s.getReg .x21=256) (lt : (s.getReg .x29+1).toNat<(s.getReg .x30).toNat) (zero : s.getReg .x29-1≠0) :
    Runs (Trunc.wireImage true) s ((if true then cleared s else s).setPC (loc 1047)) 10 10 := by
  have h0:=jump s false (s.getReg .x29) 252 1026 3096 (by decide) (by rfl) (by decide)
  have h1:=add s false (s.getReg .x29) (s.getReg .x29+1) 1026 1027 1 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h2:=ge s (s.getReg .x29+1) 1027 1028 52 (by decide) (by rfl) (by rw [if_neg (not_not_intro lt)];decide)
  have h3:=add s false (s.getReg .x29+1) (s.getReg .x29-1) 1028 1029 4094 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h4:=nz s (s.getReg .x29-1) 1029 1035 24 (by decide) (by rfl) (by rw [if_pos zero];decide)
  have h5:=nop s false (s.getReg .x29-1) 1035 1036 (by decide) (by rfl) (by decide)
  have h6:=mask s scratch (s.getReg .x29-1) 1036 1037 (by decide) (by rfl) (by decide)
  have h7:=jump s true (s.getReg .x29-1) 1037 1038 4 (by decide) (by rfl) (by decide)
  have h8:=add s true (s.getReg .x29-1) (s.getReg .x29) 1038 1039 1 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h9:=jump s true (s.getReg .x29) 1039 1047 32 (by decide) (by rfl) (by decide)
  have h : Runs (Trunc.wireImage true) (ghost s false (s.getReg .x29) 252) (ghost s true (s.getReg .x29) 1047) 10 10 := (chain (chain (chain (chain (chain (chain (chain (chain (chain h0 h1) h2) h3) h4) h5) h6) h7) h8) h9)
  rwa [atStart s 252 pc,atEnd] at h

theorem top (s : MachineState) (pc : s.pc=loc 252) (scratch : s.getReg .x21=256) (lt : (s.getReg .x29+1).toNat<(s.getReg .x30).toNat) (zero : s.getReg .x29-1=0) (slot : s.getReg .x19=0) :
    Runs (Trunc.wireImage true) s ((if false then cleared s else s).setPC (loc 1047)) 10 10 := by
  have h0:=jump s false (s.getReg .x29) 252 1026 3096 (by decide) (by rfl) (by decide)
  have h1:=add s false (s.getReg .x29) (s.getReg .x29+1) 1026 1027 1 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h2:=ge s (s.getReg .x29+1) 1027 1028 52 (by decide) (by rfl) (by rw [if_neg (not_not_intro lt)];decide)
  have h3:=add s false (s.getReg .x29+1) (s.getReg .x29-1) 1028 1029 4094 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h4:=nz s (s.getReg .x29-1) 1029 1030 24 (by decide) (by rfl) (by rw [if_neg (not_not_intro zero)];decide)
  have h5:=slotZero s (s.getReg .x29-1) 1030 1033 12 (by decide) (by rfl) (by rw [if_pos slot];decide)
  have h6:=nop s false (s.getReg .x29-1) 1033 1034 (by decide) (by rfl) (by decide)
  have h7:=jump s false (s.getReg .x29-1) 1034 1038 16 (by decide) (by rfl) (by decide)
  have h8:=add s false (s.getReg .x29-1) (s.getReg .x29) 1038 1039 1 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h9:=jump s false (s.getReg .x29) 1039 1047 32 (by decide) (by rfl) (by decide)
  have h : Runs (Trunc.wireImage true) (ghost s false (s.getReg .x29) 252) (ghost s false (s.getReg .x29) 1047) 10 10 := (chain (chain (chain (chain (chain (chain (chain (chain (chain h0 h1) h2) h3) h4) h5) h6) h7) h8) h9)
  rwa [atStart s 252 pc,atEnd] at h

theorem pair (s : MachineState) (pc : s.pc=loc 252) (scratch : s.getReg .x21=256) (lt : (s.getReg .x29+1).toNat<(s.getReg .x30).toNat) (zero : s.getReg .x29-1=0) (slot : s.getReg .x19≠0) :
    Runs (Trunc.wireImage true) s ((if true then cleared s else s).setPC (loc 1047)) 10 10 := by
  have h0:=jump s false (s.getReg .x29) 252 1026 3096 (by decide) (by rfl) (by decide)
  have h1:=add s false (s.getReg .x29) (s.getReg .x29+1) 1026 1027 1 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h2:=ge s (s.getReg .x29+1) 1027 1028 52 (by decide) (by rfl) (by rw [if_neg (not_not_intro lt)];decide)
  have h3:=add s false (s.getReg .x29+1) (s.getReg .x29-1) 1028 1029 4094 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h4:=nz s (s.getReg .x29-1) 1029 1030 24 (by decide) (by rfl) (by rw [if_neg (not_not_intro zero)];decide)
  have h5:=slotZero s (s.getReg .x29-1) 1030 1031 12 (by decide) (by rfl) (by rw [if_neg slot];decide)
  have h6:=mask s scratch (s.getReg .x29-1) 1031 1032 (by decide) (by rfl) (by decide)
  have h7:=jump s true (s.getReg .x29-1) 1032 1038 24 (by decide) (by rfl) (by decide)
  have h8:=add s true (s.getReg .x29-1) (s.getReg .x29) 1038 1039 1 (by decide) (by rfl) (by decide) (by simp [signExtend12,BitVec.sub_eq_add_neg,BitVec.add_assoc] <;> rfl)
  have h9:=jump s true (s.getReg .x29) 1039 1047 32 (by decide) (by rfl) (by decide)
  have h : Runs (Trunc.wireImage true) (ghost s false (s.getReg .x29) 252) (ghost s true (s.getReg .x29) 1047) 10 10 := (chain (chain (chain (chain (chain (chain (chain (chain (chain h0 h1) h2) h3) h4) h5) h6) h7) h8) h9)
  rwa [atStart s 252 pc,atEnd] at h

theorem runGuard (s : MachineState) (pc : s.pc=loc 252) (scratch : s.getReg .x21=256) :
    Runs (Trunc.wireImage true) s ((if guardTest s then cleared s else s).setPC (loc 1047)) 10 10 := by
  by_cases lt : (s.getReg .x29+1).toNat<(s.getReg .x30).toNat
  · by_cases z : s.getReg .x29-1=0
    · by_cases sl : s.getReg .x19=0
      · simpa only [guardTest,lt,z,sl,ne_eq,not_true_eq_false,or_self,and_false,Bool.false_eq_true,ite_false] using top s pc scratch lt z sl
      · rw [if_pos ⟨lt,Or.inr sl⟩];exact pair s pc scratch lt z sl
    · rw [if_pos ⟨lt,Or.inl z⟩];exact interior s pc scratch lt z
  · rw [if_neg (fun h=>lt h.1)];exact early s pc scratch lt

end CommitGolfCandidate.Trunc.Guard
