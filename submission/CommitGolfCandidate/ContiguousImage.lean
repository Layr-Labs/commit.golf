import CommitGolfCandidate.ContiguousTree

/-! Link every carried-input execution premise to the submitted instruction
image. The generic bridges cannot certify a different instruction stream. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem contiguous_image_entry : ContiguousEntryFetched (submission.image .commit) := by
  intro state
  constructor
  · intro pc
    apply commit_fetch state 46 _ (by decide) pc
    rfl
  · intro pc
    apply commit_fetch state 54 _ (by decide) pc
    rfl

/-- The four real salt stores use x10; each intervening load uses x18. -/
theorem contiguous_image_salt : ContiguousSaltFetched (submission.image .commit) := by
  intro state i hi pc
  apply commit_fetch state (90 + i) _ (by omega)
  · simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pc
  · interval_cases i <;> rfl

/-- All seven prefix blocks select x10+32, query, then advance x10. -/
theorem contiguous_image_prefix : ContiguousPrefixFetched (submission.image .commit) := by
  intro state block bounded
  constructor
  · intro pc
    apply commit_fetch state (98 + 3 * block) _ (by omega)
    · rw [show 4096 + 4 * (98 + 3 * block) = 4488 + 12 * block by omega]
      exact pc
    · interval_cases block <;> rfl
  constructor
  · intro pc
    apply commit_fetch state (99 + 3 * block) _ (by omega)
    · rw [show 4096 + 4 * (99 + 3 * block) = 4492 + 12 * block by omega]
      exact pc
    · interval_cases block <;> rfl
  · intro pc
    apply commit_fetch state (100 + 3 * block) _ (by omega)
    · rw [show 4096 + 4 * (100 + 3 * block) = 4496 + 12 * block by omega]
      exact pc
    · interval_cases block <;> rfl

/-- The final reply falls through to the fused latch. -/
theorem contiguous_image_tail : ContiguousTailFetched (submission.image .commit) := by
  intro state
  refine ⟨?_, ?_, ?_⟩
  · intro pc
    apply commit_fetch state 119 _ (by decide) pc
    rfl
  · intro pc
    apply commit_fetch state 120 _ (by decide) pc
    rfl
  · intro pc
    apply commit_fetch state 121 _ (by decide) pc
    rfl

theorem contiguous_image_latch : ContiguousLatchFetched (submission.image .commit) := by
  intro state i hi pc
  apply commit_fetch _ (122 + i) _ (by omega)
  · interval_cases i <;>
      simp [contiguousLatchPrefix, contiguousLatchInstructions, execInstrBr, pc, MachineState.setPC]
  · interval_cases i <;> rfl

theorem contiguous_image_exit : ContiguousExitFetched (submission.image .commit) := by
  intro state pc
  apply commit_fetch state 125 _ (by decide) pc
  rfl

theorem fused_image_peeled : ParentTripleFetched (submission.image .commit) 4388 := by
  intro state
  refine ⟨?_, ?_, ?_⟩
  · intro pc
    apply commit_fetch state 73 _ (by decide) pc
    rfl
  · intro pc
    apply commit_fetch state 74 _ (by decide) pc
    rfl
  · intro pc
    apply commit_fetch state 75 _ (by decide) pc
    rfl
theorem fused_image_first : ParentTripleFetched (submission.image .commit) 4316 := by
  intro state
  refine ⟨?_, ?_, ?_⟩
  · intro pc
    apply commit_fetch state 55 _ (by decide) pc
    rfl
  · intro pc
    apply commit_fetch state 56 _ (by decide) pc
    rfl
  · intro pc
    apply commit_fetch state 57 _ (by decide) pc
    rfl
theorem fused_image_second : ParentTripleFetched (submission.image .commit) 4328 := by
  intro state
  refine ⟨?_, ?_, ?_⟩
  · intro pc
    apply commit_fetch state 58 _ (by decide) pc
    rfl
  · intro pc
    apply commit_fetch state 59 _ (by decide) pc
    rfl
  · intro pc
    apply commit_fetch state 60 _ (by decide) pc
    rfl
theorem fused_image_peel_branch : PeeledBranchFetched (submission.image .commit) := by
  intro state pc
  apply commit_fetch state 76 _ (by decide) pc
  rfl

theorem fused_image_pair_branch : PairedBranchFetched (submission.image .commit) := by
  intro state pc
  apply commit_fetch state 61 _ (by decide) pc
  rfl

theorem fused_image_parent_exit : ParentExitFetched (submission.image .commit) := by
  intro state
  constructor
  · intro pc
    apply commit_fetch state 62 _ (by decide) pc
    rfl
  · intro pc
    apply commit_fetch state 77 _ (by decide) pc
    rfl

theorem fused_image_parents : FusedParentFetched (submission.image .commit) :=
  ⟨fused_image_peeled, fused_image_first, fused_image_second,
    fused_image_peel_branch, fused_image_pair_branch, fused_image_parent_exit⟩

end CommitGolfCandidate
