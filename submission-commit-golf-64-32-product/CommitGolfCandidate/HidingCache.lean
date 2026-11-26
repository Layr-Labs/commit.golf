import CommitGolfCandidate.HidingCompression

/-! A fixed transcript of prior compression answers can be handled by intercepting
cached queries. This preserves the exact continuation distribution and never
increases its public-query budget. No restriction is made on private randomness. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingCacheDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

/-- Replay known compression answers locally; forward every other query. -/
def cacheAnswers (cache : CompressionCache) {α : Type}
    (computation : OracleComp World α) : OracleComp World α :=
  OracleComp.recOn computation pure fun query _ next =>
    match query with
    | .inr (.inl input) =>
        match cache input with
        | some answer => next answer
        | none => do
            let answer ← (liftM (World.query (.inr (.inl input))) : OracleComp World _)
            next answer
    | .inl coins => do
        let answer ← (liftM (World.query (.inl coins)) : OracleComp World _)
        next answer
    | .inr (.inr permQuery) => do
        let answer ← (liftM (World.query (.inr (.inr permQuery))) : OracleComp World _)
        next answer

theorem cache_answers_pure (cache : CompressionCache) {α : Type} (value : α) :
    cacheAnswers cache (pure value) = pure value := rfl

theorem cache_answers_bound (cache : CompressionCache) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) :
    PublicQueryBound (cacheAnswers cache computation) budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩
    · rcases publicQuery with input | permQuery
      · cases cached : cache input with
        | none =>
          change PublicQueryBound
            (match cache input with
             | some answer => cacheAnswers cache (next answer)
             | none => (liftM (World.query (.inr (.inl input))) : OracleComp World _) >>=
                 fun answer => cacheAnswers cache (next answer)) budget
          rw [cached]
          exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩
        | some answer =>
          change PublicQueryBound
            (match cache input with
             | some answer => cacheAnswers cache (next answer)
             | none => (liftM (World.query (.inr (.inl input))) : OracleComp World _) >>=
                 fun answer => cacheAnswers cache (next answer)) budget
          rw [cached]
          exact (ih answer _ (bounded.2 answer)).mono (Nat.sub_le _ _)
      · exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩

/-- Replaying the cache inside the continuation is exactly the same as extending
the sampled oracle table with those prior answers. -/
theorem fixed_cache_answers (cache : CompressionCache) (oracle : Oracle) {α : Type}
    (computation : OracleComp World α) :
    fixedOracleRun oracle (cacheAnswers cache computation) =
      fixedOracleRun ⟨tableExtending cache oracle.compression, oracle.permutation⟩ computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rw [cache_answers_pure, fixed_oracle_run_pure, fixed_oracle_run_pure]
  | query_bind query next ih =>
    rcases query with coins | publicQuery
    · change fixedOracleRun oracle
        ((liftM (World.query (.inl coins)) : OracleComp World _) >>=
          fun answer => cacheAnswers cache (next answer)) = _
      rw [fixed_oracle_run_private, fixed_oracle_run_private]
      exact bind_congr ih
    · rcases publicQuery with input | permQuery
      · change fixedOracleRun oracle
          (match cache input with
           | some answer => cacheAnswers cache (next answer)
           | none => (liftM (World.query (.inr (.inl input))) : OracleComp World _) >>=
               fun answer => cacheAnswers cache (next answer)) = _
        rw [fixed_oracle_run_public]
        cases cached : cache input with
        | none =>
          rw [fixed_oracle_run_public, ih]
          congr 2
          change oracle.compression input = (cache input).getD (oracle.compression input)
          rw [cached]
          rfl
        | some answer =>
          rw [ih]
          congr 2
          change answer = (cache input).getD (oracle.compression input)
          rw [cached]
          rfl
      · change fixedOracleRun oracle
          ((liftM (World.query (.inr (.inr permQuery))) : OracleComp World _) >>=
            fun answer => cacheAnswers cache (next answer)) = _
        rw [fixed_oracle_run_public, fixed_oracle_run_public, ih]
        cases permQuery <;> rfl

/-- A fresh salt can hit a previously answered cell only by guessing one of the
low halves of the cached inputs. The block may depend on the earlier transcript. -/
theorem cached_salt_hit_bound (cache : CompressionCache) (keys : Finset (BitVec 512))
    (covered : ∀ input, cache input ≠ none → input ∈ keys) (block : Digest) :
    (prEvent ((fun salt : Digest => cache (block ++ salt) ≠ none) <$> (($ᵗ Digest)))) ≤
      (keys.card : ENNReal) / 2^256 := by
  have included :
      (prEvent ((fun salt : Digest => cache (block ++ salt) ≠ none) <$> (($ᵗ Digest)))) ≤
      (prEvent ((fun salt : Digest => keys.toList.any
        (fun input => decide (input.extractLsb' 0 256 = salt)) = true) <$> (($ᵗ Digest)))) := by
    apply prEvent_mono_of_support
    intro salt _ hit
    apply List.any_eq_true.mpr
    exact ⟨block ++ salt, Finset.mem_toList.mpr (covered _ hit),
      decide_eq_true (BitVec.extractLsb'_append_eq_right)⟩
  exact included.trans (by simpa only [Finset.length_toList] using
    fresh_trace_hit_probability keys.toList)

/-- The single-compression hiding step remains valid after fixing a prior cache.
Its loss is the continuation's query budget plus the number of cached inputs,
all divided by 2^256. Thus prior queries are charged rather than ignored. -/
theorem cached_salted_compression_distance (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec 512)) (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (block : Digest) {α : Type} (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ Digest
          let oracle : Oracle := ⟨tableExtending cache table, permutation⟩
          fixedOracleRun oracle (next (combine oracle.compression salt block)))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next answer)) ≤
      ((keys.card + budget : Nat) : ℝ) / 2^256 := by
  let intermediate : ProbComp α := do
    let table ← $ᵗ Compression
    let salt ← $ᵗ Digest
    fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next (combine table salt block))
  have prior : measureTVDist
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ Digest
          let oracle : Oracle := ⟨tableExtending cache table, permutation⟩
          fixedOracleRun oracle (next (combine oracle.compression salt block)))
      intermediate ≤ ((keys.card : ENNReal) / 2^256).toReal := by
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression) _ _ (by positivity)
    intro table
    refine (measureTVDist_bind_left_le_prEvent_of_evalDistEq ($ᵗ Digest) _ _
      (fun salt => cache (block ++ salt) ≠ none) ?_).trans ?_
    · intro salt unqueried
      have empty : cache (block ++ salt) = none := Classical.not_not.mp unqueried
      have same : combine (tableExtending cache table) salt block = combine table salt block := by
        change (cache (block ++ salt)).getD (table (block ++ salt)) = table (block ++ salt)
        rw [empty]
        rfl
      dsimp only
      rw [same]
    · exact ENNReal.toReal_mono (by finiteness) (cached_salt_hit_bound cache keys covered block)
  have after := salted_compression_distance permutation block
    (fun answer => cacheAnswers cache (next answer)) budget
    (fun answer => cache_answers_bound cache (next answer) budget (bounded answer))
  simp only [fixed_cache_answers] at after
  refine ((measureTVDist_triangle _ intermediate _).trans (add_le_add prior after)).trans ?_
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, Nat.cast_add]
  exact le_of_eq (add_div _ _ _).symm

end CommitGolfCandidate
