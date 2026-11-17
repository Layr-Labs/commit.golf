import CommitGolfCandidate.CapCheckPathCopies

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capWordCopyPrefix capCheckPathBranchState

private theorem zero_offset (word : Fin 4) :
    signExtend12 (BitVec.ofNat 12 (0+8*word.val)) =
      BitVec.ofNat 64 (8*word.val) := by
  fin_cases word <;> decide

private theorem scratch_access (state : MachineState) (scratch : state.getReg .x21 = 256)
    (offset : Nat) (allowed : offset = 0 ∨ offset = 32) :
    ∀ word : Fin 4,
      accessValid (state.getReg .x21 +
        signExtend12 (BitVec.ofNat 12 (offset+8*word.val))) 8 = true := by
  intro word
  rw [scratch]
  rcases allowed with rfl | rfl <;> fin_cases word <;> decide

theorem cap_check_path_preparation_execute (state : MachineState) (pc : state.pc = 4272)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8*word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check)
      (capCheckPathPreparationSteps (state.getReg .x20)+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckPathPreparedState state) allowCoins
          return result.charge (capCheckPathPreparationSteps (state.getReg .x20)) 0) := by
  let branched := capCheckPathBranchState state
  have scratchB : branched.getReg .x21 = 256 :=
    (cap_check_path_branch_register state .x21 (by decide)).trans scratch
  have sourceB : ∀ word : Fin 4,
      accessValid (branched.getReg .x25 +
        signExtend12 (BitVec.ofNat 12 (0+8*word.val))) 8 = true := by
    intro word
    rw [zero_offset word, cap_check_path_branch_register state .x25 (by decide)]
    exact sourceValid word
  by_cases even : state.getReg .x20 &&& 1 = 0
  · have branchPC : branched.pc = 4348 := by
      unfold branched capCheckPathBranchState
      simp only [MachineState.setPC, if_pos even]
    simp only [capCheckPathPreparationSteps, if_pos even, capCheckPathPreparedState]
    rw [show 10+fuel = 2+(8+fuel) by omega,
      cap_check_path_branch_execute state pc,
      cap_word_copy_execute _ .x25 .x21 0 32 4348 cap_check_path_copy_even_fetched
        branched branchPC (by decide) (by decide) sourceB
        (scratch_access branched scratchB 32 (Or.inr rfl))]
    simp [Execution.charge, ← Nat.add_assoc, branched]
  · have branchPC : branched.pc = 4280 := by
      unfold branched capCheckPathBranchState
      simp only [MachineState.setPC, if_neg even]
    let first := capWordCopyPrefix .x21 .x21 0 32 branched 8
    let both := capWordCopyPrefix .x25 .x21 0 0 first 8
    have firstPC : first.pc = 4312 := by
      unfold first
      rw [cap_word_copy_prefix_pc _ _ _ _ _ 8 (by decide), branchPC]
      rfl
    have firstScratch : first.getReg .x21 = 256 :=
      (cap_word_copy_prefix_register _ _ _ _ _ 8 (by decide) .x21 (by decide)).trans scratchB
    have firstSource : ∀ word : Fin 4,
        accessValid (first.getReg .x25 +
          signExtend12 (BitVec.ofNat 12 (0+8*word.val))) 8 = true := by
      simpa only [first, cap_word_copy_prefix_register _ _ _ _ _ 8
        (by decide) .x25 (by decide)] using sourceB
    have bothPC : both.pc = 4344 := by
      unfold both
      rw [cap_word_copy_prefix_pc _ _ _ _ _ 8 (by decide), firstPC]
      rfl
    simp only [capCheckPathPreparationSteps, if_neg even, capCheckPathPreparedState]
    rw [show 19+fuel = 2+(8+(8+(1+fuel))) by omega,
      cap_check_path_branch_execute state pc,
      cap_word_copy_execute _ .x21 .x21 0 32 4280 cap_check_path_copy_current_fetched
        branched branchPC (by decide) (by decide)
        (scratch_access branched scratchB 0 (Or.inl rfl))
        (scratch_access branched scratchB 32 (Or.inr rfl)),
      cap_word_copy_execute _ .x25 .x21 0 0 4312 cap_check_path_copy_odd_fetched
        first firstPC (by decide) (by decide) firstSource
        (scratch_access first firstScratch 0 (Or.inl rfl)),
      cap_check_path_jump_execute both bothPC]
    simp [Execution.charge, ← Nat.add_assoc, both, first, branched]

end CommitGolfCandidate
