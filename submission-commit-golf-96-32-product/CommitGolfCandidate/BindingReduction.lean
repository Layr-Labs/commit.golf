import VCVio.OracleComp.EvalDist.Sum
import CommitGolfCandidate.BindingReplay

/-! Probability-preserving reduction from the submitted machine's binding game
to finding a compression collision. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp

/-- Run the reduction against the same independently sampled primitives as the
binding game. Its budget includes the original adversary and at most 296 replay calls. -/
noncomputable def collisionGame (adversary : Scheme.Adversary) :
    ProbComp (Oracle × List (BitVec COMPRESSION_INPUT_LENGTH) × Nat) := do
  let oracle ← Oracle.sample
  let (inputs, calls) ← oracle.run (bindingExtractor adversary)
  return (oracle, inputs, calls)

theorem binding_probability_le_collision (adversary : Scheme.Adversary) (queryBudget : Nat) :
    (prEvent ((fun (oracle, claim, calls) => submission.scheme.Breaks oracle claim ∧ calls ≤ queryBudget) <$> (Scheme.bindingGame adversary))) ≤
    (prEvent ((fun (oracle, inputs, calls) => HasCompressionCollision oracle.compression inputs ∧
        calls ≤ queryBudget + 296) <$> (collisionGame adversary))) := by
  simp only [Scheme.bindingGame, collisionGame, binding_extractor_run,
    bind_pure_comp]
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro oracle
  apply mul_le_mul' le_rfl
  simp only [prEvent_map, Function.comp_def]
  apply prEvent_mono_of_support
  intro result _ winning
  exact ⟨breaks_replay_collision oracle result.1 winning.1,
    Nat.add_le_add winning.2 (replay_claim_cost_le result.1)⟩

/-- Once the query budget reaches 2^120, the required upper bound is at least
one. No collision estimate is needed in this range. -/
theorem binding_large_budget (adversary : Scheme.Adversary) (queryBudget : Nat)
    (large : 2 ^ BINDING_SECURITY_BITS ≤ queryBudget) :
    (prEvent ((fun (oracle, claim, calls) => submission.scheme.Breaks oracle claim ∧ calls ≤ queryBudget) <$> (Scheme.bindingGame adversary))) ≤ (queryBudget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  apply le_trans (prEvent_le_one _)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
  simpa using (show ((2 ^ BINDING_SECURITY_BITS : Nat) : ENNReal) ≤ queryBudget from
    Nat.cast_le.mpr large)

/-- The 296-query replay fits inside the security margin between a 256-bit output
and the challenge's 120-bit target, even with a loose quadratic birthday bound. -/
theorem replay_birthday_arithmetic (queryBudget : Nat)
    (positive : 1 ≤ queryBudget) (small : queryBudget ≤ 2 ^ 120) :
    (queryBudget + 296) ^ 2 ≤ queryBudget * 2 ^ 136 := by
  have quadratic : queryBudget * queryBudget ≤ queryBudget * 2 ^ 120 :=
    Nat.mul_le_mul_left queryBudget small
  have h1 : (queryBudget + 296) ^ 2 = queryBudget * queryBudget + 592 * queryBudget + 87616 := by ring
  have h2 : 87616 ≤ 87616 * queryBudget := by omega
  have h3 : queryBudget * 2 ^ 120 + 592 * queryBudget + 87616 * queryBudget =
      queryBudget * (2 ^ 120 + 592 + 87616) := by ring
  have h4 : queryBudget * (2 ^ 120 + 592 + 87616) ≤ queryBudget * 2 ^ 136 :=
    Nat.mul_le_mul_left queryBudget (by decide)
  omega

theorem replay_birthday_le_binding_target (queryBudget : Nat)
    (positive : 1 ≤ queryBudget) (small : queryBudget ≤ 2 ^ BINDING_SECURITY_BITS) :
    ((queryBudget : ENNReal) + 296) ^ 2 / 2 ^ 256 ≤
      (queryBudget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
  have arithmetic : ((queryBudget : ENNReal) + 296) ^ 2 ≤ (queryBudget : ENNReal) * 2 ^ 136 := by
    exact_mod_cast replay_birthday_arithmetic queryBudget positive small
  calc
    _ ≤ (queryBudget : ENNReal) * 2 ^ 136 / 2 ^ 256 :=
      ENNReal.div_le_div_right arithmetic _
    _ = (queryBudget : ENNReal) / 2 ^ BINDING_SECURITY_BITS := by
      change (queryBudget : ENNReal) * 2 ^ 136 / 2 ^ 256 = (queryBudget : ENNReal) / 2 ^ 120
      rw [show (2 : ENNReal) ^ 256 = 2 ^ 120 * 2 ^ 136 by rw [← pow_add]]
      exact ENNReal.mul_div_mul_right _ _ (by positivity) (by finiteness)

end CommitGolfCandidate
