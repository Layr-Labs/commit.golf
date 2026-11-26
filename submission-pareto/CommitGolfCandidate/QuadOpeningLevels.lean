import CommitGolfCandidate.QuadOpeningTriple

/-! The record levels 0-6 of one level-7 cap penta record: the pairs `(0,1)`, `(2,3)` and the
triple `(4,5,6)`. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling

/-- Levels `0 … 6`. -/
def levelsRun (state : MachineState) : MachineState :=
  tripleRun (pairRun 1 (pairRun 0 state))

theorem levels_run (init : MachineState) (positions : Positions) (o : Nat)
    (inside : ordinalIndex positions o < LENGTH) (ordinal : o < LENGTH) (state : MachineState)
    (at_ : LevelAt init state positions o 0) :
      Runs state (levelsRun state) 263 290 ∧ LevelAt init (levelsRun state) positions o 7 ∧
      ∀ r, r ≠ .x27 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x21 → r ≠ .x24 → r ≠ .x25 → r ≠ .x30 →
        r ≠ .x31 → (levelsRun state).getReg r = state.getReg r := by
  obtain ⟨run₀, at₀, regs₀⟩ := pair_level_step init state positions o 0 (by decide) inside ordinal at_
  obtain ⟨run₁, at₁, regs₁⟩ := pair_level_step init _ positions o 1 (by decide) inside ordinal at₀
  obtain ⟨run₂, at₂, regs₂⟩ := triple_level_step init _ positions o inside ordinal at₁
  refine ⟨(run₀.trans (run₁.trans run₂)).cast (by simp) (by simp), at₂, ?_⟩
  intro r a b c d e f g h l m
  unfold levelsRun
  rw [regs₂ r a b c d e f g h l m, regs₁ r a b c d e f g h l m, regs₀ r a b c d e f g h l m]

end TwoPermutationPrototype.QuadOpening
