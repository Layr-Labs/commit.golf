import CommitGolfCandidate.ReconstructedHonestBudget

namespace CommitGolfCandidate.Reconstruction.HonestFuel
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem positive (i : Instruction) : 1 ≤ instructionCycles i := by
  cases i with
  | base op => cases op <;> simp [instructionCycles]
  | word op _ _ _ => cases op <;> simp [instructionCycles]
  | sraiw _ _ _ => exact Nat.le_refl 1

private theorem queried (q : PublicSpec.Domain) : 1≤oracleCycles q := by cases q <;> exact (by decide : 1≤8)

/-- An unfinished execution has used every unit of fuel, each costing at least one cycle. -/
theorem charged (im : Image) (fuel : Nat) (s : MachineState) (coins : Bool) (r : Execution)
    (run : r∈support (execute im fuel s coins)) (alive : r.exit=.unfinished) : fuel≤r.cycles := by
  induction fuel generalizing s r with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    simp only [execute] at run
    split at run
    · simp only [support_pure,Set.mem_singleton_iff] at run; subst r; cases alive
    · split at run
      · split at run
        · simp only [support_pure,Set.mem_singleton_iff] at run; subst r; cases alive
        · simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at run
          obtain ⟨_,_,tail,sub,rfl⟩ := run
          have used := ih _ tail sub alive
          have cost := queried (by assumption)
          simp only [Execution.charge]; omega
      · split at run
        · simp only [support_pure,Set.mem_singleton_iff] at run; subst r
          split at alive <;> cases alive
        · split at run
          · simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at run
            obtain ⟨_,_,tail,rest,rfl⟩ := run
            have used := ih _ tail rest alive
            simp only [Execution.charge]; omega
          · simp only [support_pure,Set.mem_singleton_iff] at run; subst r; cases alive
    · split at run
      · simp only [support_pure,Set.mem_singleton_iff] at run; subst r; cases alive
      · simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at run
        obtain ⟨tail,rest,rfl⟩ := run
        have used := ih _ tail rest alive
        have cost := positive (by assumption)
        simp only [Execution.charge]; omega

end CommitGolfCandidate.Reconstruction.HonestFuel
