import CommitGolfCandidate.Probability
import CommitGolfCandidate.HidingTrace
import VCVio.OracleComp.EvalDist.Sum

/-! An independently hidden salt is hit by at most q adaptive queries with
probability at most q/2^256. Adaptivity is handled by recording the entire
unprogrammed run before averaging over the independent salt. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingHiddenQueryDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleComp.DeferredSampling

private theorem uniform_list_guess (width : Nat) (guesses : List (BitVec width)) :
    (prEvent ((fun value => value ∈ guesses) <$> (($ᵗ BitVec width)))) ≤
      (guesses.length : ENNReal) / 2^width := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have selected : (Finset.univ.filter fun value => value ∈ guesses) = guesses.toFinset := by
    ext value
    simp
  have cardinal : Fintype.card (BitVec width) = 2^width := by simp
  rw [selected, cardinal]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_div_right
  exact Nat.cast_le.mpr (List.toFinset_card_le guesses)

theorem fresh_trace_hit_probability (trace : List (BitVec COMPRESSION_INPUT_LENGTH)) :
    (prEvent ((fun salt : Digest => trace.any (fun input => decide (input.extractLsb' 0 256 = salt)) = true) <$> (($ᵗ Digest)))) ≤ (trace.length : ENNReal) / 2^256 := by
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
    (prEvent ((fun result : α × Unit × Bool => result.2.2 = true) <$> ((($ᵗ Digest) >>= fun salt => flaggedRun oracle (marksSalt salt) computation)))) ≤
      (budget : ENNReal) / 2^256 := by
  letI : MeasurableSpace (α × Unit × Bool) := ⊤
  have reordered :
      𝒟[($ᵗ Digest) >>= fun salt => flaggedRun oracle (marksSalt salt) computation] =
      𝒟[do let traced ← fixedOracleRun oracle (traceCompression computation)
           let salt ← $ᵗ Digest
           pure (traced.1, (), traced.2.any (fun input => decide (input.extractLsb' 0 256 = salt)))] := by
    simp only [flagged_run_trace, Bool.false_or, map_eq_bind_pure_comp]
    exact distribution_bind_comm ($ᵗ Digest) (fixedOracleRun oracle (traceCompression computation)) _
  have probability := (EvalDistEq.of_evalDist_eq reordered).prEvent_eq
    (fun result => result.2.2 = true)
  rw [probability]
  apply prEvent_bind_le_of_forall_le_of_support
  intro traced reached
  rw [bind_pure_comp, prEvent_map]
  refine (fresh_trace_hit_probability traced.2).trans ?_
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (trace_run_length oracle computation budget
    bounded traced reached)) _

/-- Averaging pointwise identical-until-bad bounds charges the averaged bad-event
probability. The sampled key space is finite; the observation type need not be. -/
theorem distance_bind_le_averaged_bad {Key Output : Type} [Fintype Key]
    (keys : ProbComp Key) (left right : Key → ProbComp Output)
    (tagged : Key → ProbComp (Output × Unit × Bool))
    (bounded : ∀ key, measureTVDist (left key) (right key) ≤
      (prEvent ((fun result => result.2.2 = true) <$> (tagged key))).toReal) :
    measureTVDist (keys >>= left) (keys >>= right) ≤
      (prEvent ((fun result => result.2.2 = true) <$> (keys >>= tagged))).toReal := by
  refine (measureTVDist_bind_left_le_tsum keys left right).trans ?_
  rw [tsum_fintype, prEvent_bind_eq_sum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_le_sum
    intro key _
    rw [ENNReal.toReal_mul]
    exact mul_le_mul_of_nonneg_left (bounded key) ENNReal.toReal_nonneg
  · intro key _
    exact ENNReal.mul_ne_top (prEvent_ne_top _) (prEvent_ne_top _)

/-- Programming one input with a fresh hidden low half changes any q-query
continuation by at most q/2^256 in statistical distance. The continuation may
know the programmed answer and message block, but not the hidden salt. -/
theorem hidden_reprogram_distance (oracle : Oracle) (block answer : Digest)
    {α : Type} (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) :
    measureTVDist
      (($ᵗ Digest) >>= fun _ => fixedOracleRun oracle computation)
      (($ᵗ Digest) >>= fun salt =>
        fixedOracleRun (programCompression oracle ((padInput (block ++ salt))) answer) computation) ≤
      ((budget : ENNReal) / 2^256).toReal := by
  have distance := distance_bind_le_averaged_bad ($ᵗ Digest)
    (fun _ => fixedOracleRun oracle computation)
    (fun salt => fixedOracleRun (programCompression oracle ((padInput (block ++ salt))) answer) computation)
    (fun salt => flaggedRun oracle (marksSalt salt) computation) (fun salt => by
      have result := reprogram_compression_distance oracle ((padInput (block ++ salt))) answer computation
      have low : ((padInput (block ++ salt))).extractLsb' 0 256 = salt :=
        padInput_digest block salt
      simpa only [low] using result)
  exact distance.trans (ENNReal.toReal_mono (by finiteness)
    (fresh_query_hit_bound oracle computation budget bounded))

end CommitGolfCandidate
