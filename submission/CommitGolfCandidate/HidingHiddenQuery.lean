import CommitGolfCandidate.HidingTrace
import VCVio.EvalDist.Fintype

/-! An independently hidden salt is hit by at most q adaptive queries with
probability at most q/2^256. Adaptivity is handled by recording the entire
unprogrammed run before averaging over the independent salt. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleComp.DeferredSampling

private theorem uniform_list_guess (width : Nat) (guesses : List (BitVec width)) :
    Pr[fun value => value ∈ guesses | ($ᵗ BitVec width)] ≤
      (guesses.length : ENNReal) / 2^width := by
  classical
  rw [probEvent_uniformSample]
  have selected : (Finset.univ.filter fun value => value ∈ guesses) = guesses.toFinset := by
    ext value
    simp
  have cardinal : Fintype.card (BitVec width) = 2^width := by simp
  rw [selected, cardinal]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_div_right
  exact Nat.cast_le.mpr (List.toFinset_card_le guesses)

theorem fresh_trace_hit_probability (trace : List (BitVec 512)) :
    Pr[fun salt : Digest => trace.any (fun input => decide (input.extractLsb' 0 256 = salt)) = true |
      ($ᵗ Digest)] ≤ (trace.length : ENNReal) / 2^256 := by
  have event : (fun salt : Digest =>
      trace.any (fun input => decide (input.extractLsb' 0 256 = salt)) = true) =
      (fun salt => salt ∈ trace.map (fun input => input.extractLsb' 0 256)) := by
    funext salt
    simp only [List.any_eq_true, decide_eq_true_eq, List.mem_map]
  rw [event]
  simpa only [List.length_map] using
    uniform_list_guess 256 (trace.map (fun input => input.extractLsb' 0 256))

/-- The computation may be randomized and adapt to every oracle answer. It must
not receive the separate hidden salt; its query trace is then independent of it. -/
theorem fresh_query_hit_bound (oracle : Oracle) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) :
    Pr[fun result : α × Unit × Bool => result.2.2 = true |
      (($ᵗ Digest) >>= fun salt => flaggedRun oracle (marksSalt salt) computation)] ≤
      (budget : ENNReal) / 2^256 := by
  have reordered :
      𝒮[($ᵗ Digest) >>= fun salt => flaggedRun oracle (marksSalt salt) computation] =
      𝒮[do let traced ← fixedOracleRun oracle (traceCompression computation)
           let salt ← $ᵗ Digest
           pure (traced.1, (), traced.2.any (fun input => decide (input.extractLsb' 0 256 = salt)))] := by
    simp only [flagged_run_trace, Bool.false_or, map_eq_bind_pure_comp]
    exact evalSPMF_bind_comm _ _ _
  have probability := congrArg (fun distribution : SPMF (α × Unit × Bool) =>
    Pr[fun result => result.2.2 = true | distribution]) reordered
  simp only [probEvent_evalSPMF] at probability
  rw [probability]
  apply probEvent_bind_le_of_forall_le
  intro traced reached
  rw [bind_pure_comp, probEvent_map]
  refine (fresh_trace_hit_probability traced.2).trans ?_
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (trace_run_length oracle computation budget
    bounded traced reached)) _

/-- Averaging pointwise identical-until-bad bounds charges the averaged bad-event
probability. The sampled key space is finite; the observation type need not be. -/
theorem distance_bind_le_averaged_bad {Key Output : Type} [Fintype Key]
    (keys : ProbComp Key) (left right : Key → ProbComp Output)
    (tagged : Key → ProbComp (Output × Unit × Bool))
    (bounded : ∀ key, tvDist (left key) (right key) ≤
      Pr[fun result => result.2.2 = true | tagged key].toReal) :
    tvDist (keys >>= left) (keys >>= right) ≤
      Pr[fun result => result.2.2 = true | keys >>= tagged].toReal := by
  refine (tvDist_bind_left_le keys left right).trans ?_
  rw [tsum_fintype, probEvent_bind_eq_sum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_le_sum
    intro key _
    rw [ENNReal.toReal_mul]
    exact mul_le_mul_of_nonneg_left (bounded key) ENNReal.toReal_nonneg
  · intro key _
    exact ENNReal.mul_ne_top probOutput_ne_top probEvent_ne_top

/-- Programming one input with a fresh hidden low half changes any q-query
continuation by at most q/2^256 in statistical distance. The continuation may
know the programmed answer and message block, but not the hidden salt. -/
theorem hidden_reprogram_distance (oracle : Oracle) (block answer : Digest)
    {α : Type} (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) :
    tvDist
      (($ᵗ Digest) >>= fun _ => fixedOracleRun oracle computation)
      (($ᵗ Digest) >>= fun salt =>
        fixedOracleRun (programCompression oracle (block ++ salt) answer) computation) ≤
      ((budget : ENNReal) / 2^256).toReal := by
  have distance := distance_bind_le_averaged_bad ($ᵗ Digest)
    (fun _ => fixedOracleRun oracle computation)
    (fun salt => fixedOracleRun (programCompression oracle (block ++ salt) answer) computation)
    (fun salt => flaggedRun oracle (marksSalt salt) computation) (fun salt => by
      have result := reprogram_compression_distance oracle (block ++ salt) answer computation
      have low : (block ++ salt).extractLsb' 0 256 = salt := by
        apply BitVec.eq_of_getLsbD_eq
        intro bit below
        simp only [BitVec.getLsbD_extractLsb', below, decide_true, Bool.true_and,
          Nat.zero_add, BitVec.getLsbD_append, if_true]
      simpa only [low] using result)
  exact distance.trans (ENNReal.toReal_mono (by finiteness)
    (fresh_query_hit_bound oracle computation budget bounded))

end CommitGolfCandidate
