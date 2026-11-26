import CommitGolfCandidate.ReconstructedHonestDepthControl

namespace CommitGolfCandidate.Reconstruction.CapDepthScan
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 HonestCapPlan HonestCapState HonestSizeSchedule
open TwoPermutationPrototype.RV64 HonestDepthPair
open HonestSizeRows (Rows)
set_option maxRecDepth 16384
attribute [local irreducible] ArtifactEncoding.decode execute

private theorem visit (o : Oracle) (f : Nat→Bool) (d : Nat) (pos : 0<d) (small : d≤9)
    (trap : CommitStorage.Trapdoor) (ps : Positions) (fs : List Wire.Field) (remaining : Nat) :
    ∀ j, pairs d-j=remaining → j<pairs d → ∀ s, Matches ⟨d,.scan j (prefixCount f d j)⟩ s →
      Ptr d j s → Data f d j s trap ps fs → ∃ k t, k≤18*remaining ∧ CommitExact.Segment o image k s t ∧
      Matches ⟨d,.collected (prefixCount f d (pairs d))⟩ t ∧ Data f d (pairs d) t trap ps fs := by
  induction remaining with
  | zero => intro j eq h;omega
  | succ n ih =>
    intro j eq active s known ptr data
    obtain ⟨a,u,aCap,scan,scanMatch,ptrU,dataU⟩ := pair o f d j pos small active s trap ps fs known ptr data
    obtain ⟨b,v,bCap,guard,next,ptrV,dataV⟩ := HonestDepthControl.guard o f d (j+1) pos small (by omega)
      (by omega) u trap ps fs scanMatch ptrU dataU
    have steps := CommitExact.compose scan guard
    by_cases more : j+1<pairs d
    · rw [ite_eq_left more] at next
      obtain ⟨c,t,cCap,tail,exit,final⟩ := ih (j+1) (by omega) more v next ptrV dataV
      exact ⟨a+b+c,t,by omega,CommitExact.compose steps tail,exit,final⟩
    · rw [ite_eq_right more] at next
      have last : j+1=pairs d := by omega
      rw [last] at next dataV
      exact ⟨a+b,v,by omega,steps,next,dataV⟩

/-- The real cap machine scans all physical pairs in a level, materializes the
parent occupancy row and writes every missing child ID in checker order. The
proof stream, its bit cursor, stored tree data and global registers survive. -/
theorem run (o : Oracle) (f : Nat→Bool) (d : Nat) (pos : 0<d) (small : d≤9) (s : MachineState)
    (trap : CommitStorage.Trapdoor) (ps : Positions) (fs : List Wire.Field) (known : Matches ⟨d,.level⟩ s)
    (common : CapGlobal.Common s trap ps) (rows : Rows f d 0 s) (buf : CapEvidence.Buffer s fs) :
    ∃ k t, k≤14+18*pairs d ∧ CommitExact.Segment o image k s t ∧
      Matches ⟨d,.collected (CapSchedule.pending f d).length⟩ t ∧ CapGlobal.Common t trap ps ∧
      Rows f d (pairs d) t ∧ CapSlots.Contains (memoryView t) (CapSchedule.pending f d) ∧ CapEvidence.Buffer t fs := by
  obtain ⟨a,u,aCap,begin_,matchU,ptr,data⟩ := HonestDepthControl.enter o f d pos small s trap ps fs known rows common buf
  have positive : 0<pairs d := Nat.two_pow_pos _
  obtain ⟨b,t,bCap,all,matchT,last⟩ := visit o f d pos small trap ps fs (pairs d) 0 (Nat.sub_zero _) positive u matchU ptr data
  have len : (CapSchedule.pending f d).length=prefixCount f d (pairs d) := CapOrder.prefix_length f d _
  exact ⟨a+b,t,by omega,CommitExact.compose begin_ all,len ▸ matchT,last.global,last.rows,last.slots,last.buffer⟩

end CommitGolfCandidate.Reconstruction.CapDepthScan
