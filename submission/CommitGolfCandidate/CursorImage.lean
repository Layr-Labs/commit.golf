import CommitGolfCandidate.CursorTree

/-! Link every carried-input execution premise to the submitted instruction
image. The generic bridges cannot certify a different instruction stream. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- The four real salt stores use x10; each intervening load uses x18. -/
theorem cursor_image_salt : CursorSaltFetched (submission.image .commit) := by
  intro state i hi pc
  apply commit_fetch state (46 + i) _ (by omega)
  · simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using pc
  · interval_cases i <;> rfl

/-- All seven prefix blocks select x10+32, query, then advance x10. -/
theorem cursor_image_prefix : CursorPrefixFetched (submission.image .commit) := by
  intro state block bounded
  constructor
  · intro pc
    apply commit_fetch state (90 + 3 * block) _ (by omega)
    · rw [show 4096 + 4 * (90 + 3 * block) = 4456 + 12 * block by omega]
      exact pc
    · interval_cases block <;> rfl
  constructor
  · intro pc
    apply commit_fetch state (91 + 3 * block) _ (by omega)
    · rw [show 4096 + 4 * (91 + 3 * block) = 4460 + 12 * block by omega]
      exact pc
    · interval_cases block <;> rfl
  · intro pc
    apply commit_fetch state (92 + 3 * block) _ (by omega)
    · rw [show 4096 + 4 * (92 + 3 * block) = 4464 + 12 * block by omega]
      exact pc
    · interval_cases block <;> rfl

/-- The final reply targets the heap and the return skips the old copy block. -/
theorem cursor_image_tail : CursorTailFetched (submission.image .commit) := by
  intro state
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro pc
    apply commit_fetch state 111 _ (by decide) pc
    rfl
  · intro pc
    apply commit_fetch state 112 _ (by decide) pc
    rfl
  · intro pc
    apply commit_fetch state 113 _ (by decide) pc
    rfl
  · intro pc
    apply commit_fetch state 114 _ (by decide) pc
    rfl

end CommitGolfCandidate
