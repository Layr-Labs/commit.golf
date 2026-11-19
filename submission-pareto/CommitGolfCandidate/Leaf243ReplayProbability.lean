import CommitGolfCandidate.Leaf243CombinedMargin

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp OracleComp.DeferredSampling
set_option maxRecDepth 8192
set_option exponentiation.threshold 2100

theorem pinned_replay_bound_243_of_layout (layout : PeerLeafLayout) : PinnedReplayBound := by
  intro program q calls positive small replayed bounded
  have callBound : calls≤2^121 := by omega
  have realBound : (calls : ℝ)≤2^121 := by exact_mod_cast callBound
  have pairs : (0 : ℝ)≤(calls : ℝ)*((calls : ℝ)-1) := by
    rcases Nat.eq_zero_or_pos calls with zero | pos
    · simp [zero]
    · have one : (1 : ℝ)≤calls := by exact_mod_cast pos
      exact mul_nonneg (by positivity) (by linarith)
  have gap : (0 : ℝ)<2^238-(calls : ℝ) := by
    have : (2 : ℝ)^121<2^238 := by norm_num
    linarith
  have exponent : (0 : ℝ)≤collisionExponent (2^238) calls :=
    div_nonneg (div_nonneg pairs (by norm_num)) gap.le
  have internal : (0 : ℝ)≤1-Real.exp (-collisionExponent (2^238) calls) := by
    have h := Real.exp_le_exp.mpr (neg_nonpos.mpr exponent)
    rw [Real.exp_zero] at h
    linarith
  have leaf : (0 : ℝ)≤pinnedWidthTerm 243 calls := by
    have leafGap : (0 : ℝ)<2^1600-(calls : ℝ) := by
      have : (2 : ℝ)^121<2^1600 := by norm_num
      linarith
    unfold pinnedWidthTerm
    exact div_nonneg (add_nonneg (mul_nonneg (div_nonneg pairs (by norm_num)) (by positivity))
      (by positivity)) leafGap.le
  have compression : Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      CompressionWitness result.2] ≤ ENNReal.ofReal (1-Real.exp (-collisionExponent (2^238) calls)) := by
    have exchanged := EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm) (fun compress perm =>
        fixedOracleRun ⟨compress,perm⟩ (recordRows program)))
    simp only [Oracle.sample,bind_assoc,pure_bind]
    rw [exchanged.prEvent_eq (fun result => CompressionWitness result.2)]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ =>
      fixed_permutation_product_bound p program q calls small replayed bounded
  have leaves : Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      PinnedLeafWitness result.2] ≤ ENNReal.ofReal (pinnedWidthTerm 243 calls) := by
    simp only [Oracle.sample,bind_assoc,pure_bind]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      pinned_leaf_probability_width 243 (by decide) layout compress program calls (by omega) _ le_rfl bounded
  unfold PinnedReplayEvidence
  refine (prEvent_or_le _ _ _).trans ((add_le_add compression leaves).trans ?_)
  rw [← ENNReal.ofReal_add internal leaf]
  refine (ENNReal.ofReal_le_ofReal (combined_margin_243 q calls calls positive small replayed (by omega))).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num),ENNReal.ofReal_ofNat]

end TwoPermutationPrototype.Sampling
