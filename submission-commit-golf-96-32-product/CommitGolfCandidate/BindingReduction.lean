import VCVio.OracleComp.EvalDist.Sum
import CommitGolfCandidate.BindingReplay

/-! Probability-preserving reduction from the submitted machine's binding game
to finding a compression collision. The remaining ROM theorem must bound the
extractor's collision probability; this file does not assume that bound. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp

/-- Run the reduction against the same independently sampled primitives as the
binding game. Its budget includes the original adversary and the 170-call replay. -/
noncomputable def collisionGame (adversary : Scheme.Adversary) :
    ProbComp (Oracle × List (BitVec COMPRESSION_INPUT_LENGTH) × Nat) := do
  let oracle ← Oracle.sample
  let (inputs, calls) ← oracle.run (bindingExtractor adversary)
  return (oracle, inputs, calls)

theorem binding_probability_le_collision (adversary : Scheme.Adversary) (queryBudget : Nat) :
    (prEvent ((fun (oracle, claim, calls) => submission.scheme.Breaks oracle claim ∧ calls ≤ queryBudget) <$> (Scheme.bindingGame adversary))) ≤
    (prEvent ((fun (oracle, inputs, calls) => HasCompressionCollision oracle.compression inputs ∧
        calls ≤ queryBudget + 170) <$> (collisionGame adversary))) := by
  simp only [Scheme.bindingGame, collisionGame, binding_extractor_run,
    bind_pure_comp]
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro oracle
  apply mul_le_mul' le_rfl
  simp only [prEvent_map, Function.comp_def]
  apply prEvent_mono_of_support
  intro result _ winning
  exact ⟨breaks_replay_collision oracle result.1 winning.1, Nat.add_le_add_right winning.2 170⟩

/-- Once the query budget reaches 2^120, the required upper bound is at least
one. No collision estimate is needed in this range. -/
theorem binding_large_budget (adversary : Scheme.Adversary) (queryBudget : Nat)
    (large : 2 ^ BINDING_SECURITY_BITS ≤ queryBudget) :
    (prEvent ((fun (oracle, claim, calls) => submission.scheme.Breaks oracle claim ∧ calls ≤ queryBudget) <$> (Scheme.bindingGame adversary))) ≤ (queryBudget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  apply le_trans (prEvent_le_one _)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
  simpa using (show ((2 ^ BINDING_SECURITY_BITS : Nat) : ENNReal) ≤ queryBudget from
    Nat.cast_le.mpr large)

/-- The 170-query replay fits inside the security margin between a 256-bit output
and the challenge's 120-bit target, even with a loose quadratic birthday bound. -/
theorem replay_birthday_arithmetic (queryBudget : Nat)
    (positive : 1 ≤ queryBudget) (small : queryBudget ≤ 2 ^ 120) :
    (queryBudget + 170) ^ 2 ≤ queryBudget * 2 ^ 136 := by
  have quadratic := Nat.mul_le_mul_left queryBudget small
  have constant : 28900 ≤ 28900 * queryBudget := by omega
  have gap : queryBudget * 2 ^ 120 + 29240 * queryBudget ≤ queryBudget * 2 ^ 136 := by
    have : 2 ^ 120 + 29240 ≤ 2 ^ 136 := by norm_num
    nlinarith
  nlinarith

theorem replay_birthday_le_binding_target (queryBudget : Nat)
    (positive : 1 ≤ queryBudget) (small : queryBudget ≤ 2 ^ BINDING_SECURITY_BITS) :
    ((queryBudget : ENNReal) + 170) ^ 2 / 2 ^ 256 ≤
      (queryBudget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have arithmetic : ((queryBudget : ENNReal) + 170) ^ 2 ≤ (queryBudget : ENNReal) * 2 ^ 136 := by
    exact_mod_cast replay_birthday_arithmetic queryBudget positive small
  calc
    _ ≤ (queryBudget : ENNReal) * 2 ^ 136 / 2 ^ 256 :=
      ENNReal.div_le_div_right arithmetic _
    _ = (queryBudget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
      change (queryBudget : ENNReal) * 2 ^ 136 / 2 ^ 256 = (queryBudget : ENNReal) / 2 ^ 120
      rw [show (2 : ENNReal) ^ 256 = 2 ^ 120 * 2 ^ 136 by rw [← pow_add]]
      exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

end CommitGolfCandidate
