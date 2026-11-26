import CommitGolfCandidate.LateHidingRun

/-! One compression cell whose input carries a fresh hidden field.

`key salt` is a compression input that embeds a uniform `width`-bit salt, and
`field` reads the salt back from any input. The reply at `key salt` is then a
fresh digest for every bounded continuation that is not given the salt, up to
`(cached inputs + continuation calls) / 2^width`. This is the base tree's
(dadon's c9b8af82, `HidingHiddenQuery`, `HidingCompression`, `HidingCache`)
`cached_salted_compression_distance` with the salt field made a parameter
(position and width), so that the same lemma serves a 192-bit salt at either
end of the final leaf row. -/
namespace CommitGolfCandidate.LateHiding

-- Observations retain the discrete measurable structure used by the contract.
local instance cellDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

variable {width : Nat}

private theorem uniform_list_guess (guesses : List (BitVec width)) :
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

/-- A fixed list of inputs contains the field value of a fresh salt with
probability at most its length over `2^width`. -/
theorem fresh_trace_hit_probability (field : Late.Block → BitVec width)
    (trace : List Late.Block) :
    (prEvent ((fun salt : BitVec width =>
      trace.any (fun input => decide (field input = salt)) = true) <$> (($ᵗ BitVec width)))) ≤
      (trace.length : ENNReal) / 2^width := by
  have event : (fun salt : BitVec width =>
      trace.any (fun input => decide (field input = salt)) = true) =
      (fun salt => salt ∈ trace.map field) := by
    funext salt
    simp only [List.any_eq_true, decide_eq_true_eq, List.mem_map]
  rw [event]
  simpa only [List.length_map] using uniform_list_guess (trace.map field)

/-- The computation may be randomized and adapt to every oracle answer. It must
not receive the separate hidden salt; its query trace is then independent of it. -/
theorem fresh_query_hit_bound (oracle : Oracle) (field : Late.Block → BitVec width) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) :
    (prEvent ((fun result : α × Unit × Bool => result.2.2 = true) <$>
      ((($ᵗ BitVec width) >>= fun salt =>
        flaggedRun oracle (marksInput fun input => decide (field input = salt)) computation)))) ≤
      (budget : ENNReal) / 2^width := by
  let : MeasurableSpace (α × Unit × Bool) := ⊤
  have reordered :
      𝒟[($ᵗ BitVec width) >>= fun salt =>
          flaggedRun oracle (marksInput fun input => decide (field input = salt)) computation] =
      𝒟[do let traced ← fixedOracleRun oracle (traceCompression computation)
           let salt ← $ᵗ BitVec width
           pure (traced.1, (), traced.2.any (fun input => decide (field input = salt)))] := by
    simp only [flagged_run_trace, Bool.false_or, map_eq_bind_pure_comp]
    exact distribution_bind_comm ($ᵗ BitVec width)
      (fixedOracleRun oracle (traceCompression computation)) _
  have probability := (EvalDistEq.of_evalDist_eq reordered).prEvent_eq
    (fun result => result.2.2 = true)
  rw [probability]
  apply prEvent_bind_le_of_forall_le_of_support
  intro traced reached
  rw [bind_pure_comp, prEvent_map]
  refine (fresh_trace_hit_probability field traced.2).trans ?_
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (trace_run_length oracle computation budget
    bounded traced reached)) _

/-- Programming one input that carries a fresh hidden salt changes any q-query
continuation by at most q/2^width in statistical distance. The continuation may
know the programmed answer, but not the hidden salt. -/
theorem hidden_reprogram_distance (oracle : Oracle) (key : BitVec width → Late.Block)
    (field : Late.Block → BitVec width) (field_key : ∀ salt, field (key salt) = salt)
    (answer : Late.Digest) {α : Type} (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) :
    measureTVDist
      (($ᵗ BitVec width) >>= fun _ => fixedOracleRun oracle computation)
      (($ᵗ BitVec width) >>= fun salt =>
        fixedOracleRun (programCompression oracle (key salt) answer) computation) ≤
      ((budget : ENNReal) / 2^width).toReal := by
  have distance := distance_bind_le_averaged_bad ($ᵗ BitVec width)
    (fun _ => fixedOracleRun oracle computation)
    (fun salt => fixedOracleRun (programCompression oracle (key salt) answer) computation)
    (fun salt => flaggedRun oracle (marksInput fun input => decide (field input = salt)) computation)
    (fun salt => reprogram_compression_distance oracle (key salt) answer
      (fun input => decide (field input = salt)) (decide_eq_true (field_key salt)) computation)
  exact distance.trans (ENNReal.toReal_mono (by finiteness)
    (fresh_query_hit_bound oracle field computation budget bounded))

/-- Sampling the answer first and programming its cell gives the exact joint
distribution of a uniform table and its answer, including a randomized observer. -/
theorem answer_programming (permutation : Perm) (input : Late.Block)
    {α : Type} (next : Late.Digest → OracleComp World α) :
    𝒟[do let answer ← $ᵗ Late.Digest
         let table ← $ᵗ Compression
         fixedOracleRun (programCompression ⟨table, permutation⟩ input answer) (next answer)] =
    𝒟[do let table ← $ᵗ Compression
         fixedOracleRun ⟨table, permutation⟩ (next (table input))] := by
  trans 𝒟[do let answer ← $ᵗ Late.Digest
              let table ← $ᵗ Compression
              fixedOracleRun ⟨Function.update table input answer, permutation⟩
                (next ((Function.update table input answer) input))]
  · apply _root_.evalDist_bind_congr
    intro answer
    apply _root_.evalDist_bind_congr
    intro table
    erw [Function.update_self]
    rfl
  · exact compression_table_update_bind input (fun table =>
      fixedOracleRun ⟨table, permutation⟩ (next (table input)))

/-- Exact intermediate game: a uniform hidden salt and an independent digest,
with the digest programmed at the corresponding salted compression input. -/
theorem salted_programming (permutation : Perm) (key : BitVec width → Late.Block)
    {α : Type} (next : Late.Digest → OracleComp World α) :
    𝒟[do let salt ← $ᵗ BitVec width
         let answer ← $ᵗ Late.Digest
         let table ← $ᵗ Compression
         fixedOracleRun (programCompression ⟨table, permutation⟩ (key salt) answer)
           (next answer)] =
    𝒟[do let table ← $ᵗ Compression
         let salt ← $ᵗ BitVec width
         fixedOracleRun ⟨table, permutation⟩ (next (table (key salt)))] := by
  trans 𝒟[do let salt ← $ᵗ BitVec width
              let table ← $ᵗ Compression
              fixedOracleRun ⟨table, permutation⟩ (next (table (key salt)))]
  · exact _root_.evalDist_bind_congr _ _ _ (fun salt =>
      answer_programming permutation (key salt) next)
  · exact distribution_bind_comm _ _ _

/-- A salted compression output is a fresh digest for a bounded adaptive
continuation, at cost q/2^width. The salt is private; the output is public. -/
theorem salted_distance (permutation : Perm) (key : BitVec width → Late.Block)
    (field : Late.Block → BitVec width) (field_key : ∀ salt, field (key salt) = salt)
    {α : Type} (next : Late.Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ BitVec width
          fixedOracleRun ⟨table, permutation⟩ (next (table (key salt))))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Late.Digest
          fixedOracleRun ⟨table, permutation⟩ (next answer)) ≤
      ((budget : ENNReal) / 2^width).toReal := by
  let ideal : ProbComp α := do
    let answer ← $ᵗ Late.Digest
    let table ← $ᵗ Compression
    let _salt ← $ᵗ BitVec width
    fixedOracleRun ⟨table, permutation⟩ (next answer)
  let programmed : ProbComp α := do
    let answer ← $ᵗ Late.Digest
    let table ← $ᵗ Compression
    let salt ← $ᵗ BitVec width
    fixedOracleRun (programCompression ⟨table, permutation⟩ (key salt) answer) (next answer)
  have distance : measureTVDist ideal programmed ≤ ((budget : ENNReal) / 2^width).toReal := by
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ Late.Digest) _ _ (by positivity)
    intro answer
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression) _ _ (by positivity)
    intro table
    exact hidden_reprogram_distance ⟨table, permutation⟩ key field field_key answer (next answer)
      budget (bounded answer)
  have ideal_eq : 𝒟[ideal] =
      𝒟[do let table ← $ᵗ Compression
           let answer ← $ᵗ Late.Digest
           fixedOracleRun ⟨table, permutation⟩ (next answer)] := by
    unfold ideal
    trans 𝒟[do let answer ← $ᵗ Late.Digest
                let table ← $ᵗ Compression
                fixedOracleRun ⟨table, permutation⟩ (next answer)]
    · apply _root_.evalDist_bind_congr
      intro answer
      apply _root_.evalDist_bind_congr
      intro table
      exact OracleComp.evalDist_bind_const _ _
    · exact distribution_bind_comm _ _ _
  have programmed_eq : 𝒟[programmed] =
      𝒟[do let table ← $ᵗ Compression
           let salt ← $ᵗ BitVec width
           fixedOracleRun ⟨table, permutation⟩ (next (table (key salt)))] := by
    unfold programmed
    trans 𝒟[do let salt ← $ᵗ BitVec width
                let answer ← $ᵗ Late.Digest
                let table ← $ᵗ Compression
                fixedOracleRun (programCompression ⟨table, permutation⟩ (key salt) answer)
                  (next answer)]
    · trans 𝒟[do let answer ← $ᵗ Late.Digest
                  let salt ← $ᵗ BitVec width
                  let table ← $ᵗ Compression
                  fixedOracleRun (programCompression ⟨table, permutation⟩ (key salt) answer)
                    (next answer)]
      · exact _root_.evalDist_bind_congr _ _ _ (fun _ => distribution_bind_comm _ _ _)
      · exact distribution_bind_comm _ _ _
    · exact salted_programming permutation key next
  rw [measureTVDist_comm] at distance
  simpa only [measureTVDist, ideal_eq, programmed_eq] using distance

/-- A fresh salt can hit a previously answered cell only by guessing the field
of one of the cached inputs. -/
theorem cached_salt_hit_bound (cache : CompressionCache) (keys : Finset Late.Block)
    (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (key : BitVec width → Late.Block) (field : Late.Block → BitVec width)
    (field_key : ∀ salt, field (key salt) = salt) :
    (prEvent ((fun salt : BitVec width => cache (key salt) ≠ none) <$> (($ᵗ BitVec width)))) ≤
      (keys.card : ENNReal) / 2^width := by
  have included :
      (prEvent ((fun salt : BitVec width => cache (key salt) ≠ none) <$> (($ᵗ BitVec width)))) ≤
      (prEvent ((fun salt : BitVec width => keys.toList.any
        (fun input => decide (field input = salt)) = true) <$> (($ᵗ BitVec width)))) := by
    apply prEvent_mono_of_support
    intro salt _ hit
    apply List.any_eq_true.mpr
    exact ⟨key salt, Finset.mem_toList.mpr (covered _ hit), decide_eq_true (field_key salt)⟩
  exact included.trans (by simpa only [Finset.length_toList] using
    fresh_trace_hit_probability field keys.toList)

/-- The single-cell hiding step after a fixed prior cache. Its loss is the number
of cached inputs plus the continuation's query budget, over `2^width`. -/
theorem cached_salted_distance (permutation : Perm) (cache : CompressionCache)
    (keys : Finset Late.Block) (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (key : BitVec width → Late.Block) (field : Late.Block → BitVec width)
    (field_key : ∀ salt, field (key salt) = salt)
    {α : Type} (next : Late.Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ BitVec width
          let oracle : Oracle := ⟨tableExtending cache table, permutation⟩
          fixedOracleRun oracle (next (oracle.compression (key salt))))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Late.Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next answer)) ≤
      ((keys.card + budget : Nat) : ℝ) / 2^width := by
  let intermediate : ProbComp α := do
    let table ← $ᵗ Compression
    let salt ← $ᵗ BitVec width
    fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next (table (key salt)))
  have prior : measureTVDist
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ BitVec width
          let oracle : Oracle := ⟨tableExtending cache table, permutation⟩
          fixedOracleRun oracle (next (oracle.compression (key salt))))
      intermediate ≤ ((keys.card : ENNReal) / 2^width).toReal := by
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression) _ _ (by positivity)
    intro table
    refine (measureTVDist_bind_left_le_prEvent_of_evalDistEq ($ᵗ BitVec width) _ _
      (fun salt => cache (key salt) ≠ none) ?_).trans ?_
    · intro salt unqueried
      have empty : cache (key salt) = none := Classical.not_not.mp unqueried
      have same : tableExtending cache table (key salt) = table (key salt) := by
        change (cache (key salt)).getD (table (key salt)) = table (key salt)
        rw [empty]
        rfl
      dsimp only
      rw [same]
    · exact ENNReal.toReal_mono (by finiteness)
        (cached_salt_hit_bound cache keys covered key field field_key)
  have after := salted_distance permutation key field field_key
    (fun answer => cacheAnswers cache (next answer)) budget
    (fun answer => cache_answers_bound cache (next answer) budget (bounded answer))
  simp only [fixed_cache_answers] at after
  refine ((measureTVDist_triangle _ intermediate _).trans (add_le_add prior after)).trans ?_
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, Nat.cast_add]
  exact le_of_eq (add_div _ _ _).symm

end CommitGolfCandidate.LateHiding
