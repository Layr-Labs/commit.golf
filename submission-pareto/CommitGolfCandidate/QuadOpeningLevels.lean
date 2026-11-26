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
    (at_ : LevelAt init state positions o 0 (levelStart 0)) :
      Runs state (levelsRun state) 261 288 ∧ LevelAt init (levelsRun state) positions o 7 (levelStart 7) ∧
      ∀ r, r ≠ .x27 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x21 → r ≠ .x24 → r ≠ .x25 → r ≠ .x30 →
        r ≠ .x31 → (levelsRun state).getReg r = state.getReg r := by
  let i := ordinalIndex positions o
  have v0 : i / 5^(2*0) % 25 < 25 := Nat.mod_lt _ (by decide)
  have v1 : i / 5^(2*1) % 25 < 25 := Nat.mod_lt _ (by decide)
  obtain ⟨h0, h0j⟩ := pair_head_codes 0 (by decide)
  obtain ⟨_, _, n0, n0j⟩ := pair_variant_codes 0 _ (by decide) v0
  obtain ⟨_, _, n1, n1j⟩ := pair_variant_codes 1 _ (by decide) v1
  have l0 : (nextPrep 0).length = 9 := by simp [nextPrep, pairPrep, prepWith]
  have l1 : (nextPrep 1).length = 12 := by simp [nextPrep, triplePrep]
  rw [l0] at n0j; rw [l1] at n1j
  have e0 : nextPrep 0 = pairPrep 1 := by simp [nextPrep]
  have e1 : nextPrep 1 = triplePrep := by simp [nextPrep]
  rw [e0] at n0; rw [e1] at n1
  obtain ⟨run₀, at₀, regs₀⟩ := pair_level_step init state positions o 0 _ (by decide) inside ordinal h0 h0j at_
  obtain ⟨run₁, at₁, regs₁⟩ := pair_level_step init _ positions o 1 _ (by decide) inside ordinal n0 n0j at₀
  obtain ⟨run₂, at₂, regs₂⟩ := triple_level_step init _ positions o _ inside ordinal n1 n1j at₁
  refine ⟨(run₀.trans (run₁.trans run₂)).cast (by simp) (by simp), at₂, ?_⟩
  intro r a b c d e f g h l m
  unfold levelsRun
  rw [regs₂ r a b c d e f g h l m, regs₁ r a b c d e f g h l m, regs₀ r a b c d e f g h l m]

end TwoPermutationPrototype.QuadOpening
