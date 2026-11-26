import CommitGolfCandidate.MoonBinding
import CommitGolfCandidate.HidingTrace
import Mathlib.Data.Fintype.EquivFin

/-! Core probabilistic, ROM-caching, and bottom-up tree-query primitives for the
128-bit index-tagged statistical hiding proof.
- `splitBlocks`: bijection between bulk RANDOM bits and independent 128-bit salts
- `saltsMerge` involution: exact split of salts into opened vs hidden coordinates
- `cached_salted_chain_distance`: 256-bit chaining-value hiding for leaf Calls 1..3
- `queryTree`: bottom-up r=1 tree evaluation in `OracleComp World` (`<= 78,293,674` queries)
  plus the deterministic `GoodTrace` invariant and lazy-ROM `CacheHitsPrefix` bound. -/
namespace CommitGolfCandidate

local instance moonHidingCoreDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

/-! ### 1. Bulk RANDOM Salt Splitting & Opened/Hidden Coordinate Split -/

def splitBlocks (width count : Nat) (packed : BitVec (width * count)) : Fin count → BitVec width :=
  fun index => packed.extractLsb' (width * index.val) width

theorem split_blocks_injective (width count : Nat) (pos : 0 < width) :
    Function.Injective (splitBlocks width count) := by
  intro left right same
  apply BitVec.eq_of_getLsbD_eq
  intro bit below
  have block : bit / width < count := (Nat.div_lt_iff_lt_mul pos).mpr (by simpa [Nat.mul_comm] using below)
  have offset : bit % width < width := Nat.mod_lt _ pos
  have aligned : width * (bit / width) + bit % width = bit := Nat.div_add_mod bit width
  have heq := congrArg (fun v : BitVec width => v.getLsbD (bit % width)) (congrFun same ⟨bit / width, block⟩)
  simpa only [splitBlocks, BitVec.getLsbD_extractLsb', offset, decide_true, Bool.true_and, aligned] using heq

theorem split_blocks_bijective (width count : Nat) (pos : 0 < width) :
    Function.Bijective (splitBlocks width count) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨split_blocks_injective width count pos, ?_⟩
  have hc (n : Nat) : Fintype.card (BitVec n) = 2 ^ n := Fintype.card_bitVec n
  simp only [Fintype.card_fun, Fintype.card_fin, hc]
  exact pow_mul 2 width count

theorem split_blocks_uniform_bind (width count : Nat) (pos : 0 < width)
    [SampleableType (Fin count → BitVec width)]
    {α : Type} (next : (Fin count → BitVec width) → ProbComp α) :
    𝒟[($ᵗ BitVec (width * count)) >>= fun packed => next (splitBlocks width count packed)] =
      𝒟[($ᵗ (Fin count → BitVec width)) >>= next] := by
  rw [← bind_map_left]
  exact ((SampleableType.map_uniformSample_evalDistEq_of_bijective
    (split_blocks_bijective width count pos)).bind_left next).evalDist_eq

/-- Merge opened-position salts from `sOpen` with unopened-position salts from `sHidden`. -/
def saltsMerge (positions : Positions) (sOpen sHidden : Index → Salt128) : Index → Salt128 :=
  fun i => if i ∈ positions then sOpen i else sHidden i

private theorem funMerge_uniform_bind {D R α : Type} [DecidableEq D]
    [SampleableType (D → R)] (S : Finset D) (next : (D → R) → ProbComp α) :
    𝒟[do let sOpen ← $ᵗ (D → R)
         let sHidden ← $ᵗ (D → R)
         next (fun i => if i ∈ S then sOpen i else sHidden i)] =
    𝒟[($ᵗ (D → R)) >>= next] := by
  let swap : (D → R) × (D → R) → (D → R) × (D → R) :=
    fun p => (fun i => if i ∈ S then p.1 i else p.2 i, fun i => if i ∈ S then p.2 i else p.1 i)
  have hinv : Function.Involutive swap := by
    rintro ⟨a, b⟩
    ext i <;> by_cases hi : i ∈ S <;> simp [swap, hi]
  have hswap := ((SampleableType.map_uniformSample_evalDistEq_of_bijective hinv.bijective).bind_left
    (fun p => next p.1)).evalDist_eq
  calc
    𝒟[do let sOpen ← $ᵗ (D → R)
         let sHidden ← $ᵗ (D → R)
         next (fun i => if i ∈ S then sOpen i else sHidden i)]
      = 𝒟[(do let sOpen ← $ᵗ (D → R)
              let sHidden ← $ᵗ (D → R)
              pure (sOpen, sHidden)) >>= fun p => next (swap p).1] := by
          simp only [bind_assoc, pure_bind, swap]
    _ = 𝒟[($ᵗ ((D → R) × (D → R))) >>= fun p => next (swap p).1] := by
          rw [← SampleableType.uniformSample_prod_eq_bind]
    _ = 𝒟[(swap <$> ($ᵗ ((D → R) × (D → R)))) >>= fun p => next p.1] := by
          rw [bind_map_left]
    _ = 𝒟[($ᵗ ((D → R) × (D → R))) >>= fun p => next p.1] := hswap
    _ = 𝒟[(do let sOpen ← $ᵗ (D → R)
              let sHidden ← $ᵗ (D → R)
              pure (sOpen, sHidden)) >>= fun p => next p.1] := by
          rw [SampleableType.uniformSample_prod_eq_bind]
    _ = 𝒟[do let sOpen ← $ᵗ (D → R)
             let _sHidden ← $ᵗ (D → R)
             next sOpen] := by
          simp only [bind_assoc, pure_bind]
    _ = 𝒟[($ᵗ (D → R)) >>= next] := by
          apply _root_.evalDist_bind_congr
          intro sOpen
          exact OracleComp.evalDist_bind_const _ _

theorem saltsMerge_uniform_bind (positions : Positions)
    {α : Type} (next : (Index → Salt128) → ProbComp α) :
    𝒟[do let sOpen ← $ᵗ (Index → Salt128)
         let sHidden ← $ᵗ (Index → Salt128)
         next (saltsMerge positions sOpen sHidden)] =
    𝒟[($ᵗ (Index → Salt128)) >>= next] :=
  funMerge_uniform_bind positions next

theorem uniform_coordinate_bind {D R α : Type} [DecidableEq D] [Finite D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)]
    (index : D) (next : (D → R) → ProbComp α) :
    𝒟[do let values ← $ᵗ (D → R)
         let value ← $ᵗ R
         next (Function.update values index value)] =
    𝒟[do let values ← $ᵗ (D → R); next values] := by
  have marginal : 𝒟[do let value ← $ᵗ R
                        let values ← $ᵗ (D → R)
                        pure (Function.update values index value)] = 𝒟[$ᵗ (D → R)] := by
    simpa only [bind_pure] using evalDist_uniformSample_bind_update_map
      SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample index (fun values : D → R => values)
  trans 𝒟[do let value ← $ᵗ R
              let values ← $ᵗ (D → R)
              next (Function.update values index value)]
  · exact distribution_bind_comm _ _ _
  · trans 𝒟[(do let value ← $ᵗ R
                let values ← $ᵗ (D → R)
                pure (Function.update values index value)) >>= next]
    · simp only [bind_assoc, pure_bind]
    · rw [evalDist_bind_of_discrete, marginal, ← evalDist_bind_of_discrete]

/-! ### 2. Stage-1 Lazy Sampling & Cache Interception -/

theorem staged_compression_sampling (permutation : Perm) {α β : Type}
    (first : OracleComp World α) (next : α → OracleComp World β) :
    𝒟[do let table ← $ᵗ Compression
         fixedOracleRun ⟨table, permutation⟩ (first >>= next)] =
    𝒟[do let (value, cache) ← compressionRun permutation first ∅
         let table ← $ᵗ Compression
         fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next value)] := by
  rw [← compression_sampling_empty, compression_run_bind, map_bind]
  apply _root_.evalDist_bind_congr
  rintro ⟨value, cache⟩
  exact compression_sampling_equivalence permutation (next value) cache

theorem compression_cache_covered (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) (cache : CompressionCache)
    (known : Finset CompressionSpec.Domain) (covered : ∀ key, cache key ≠ none → key ∈ known)
    (result : α × CompressionCache)
    (reached : result ∈ support (compressionRun permutation computation cache)) :
    ∃ keys : Finset CompressionSpec.Domain, keys.card ≤ known.card + budget ∧
      ∀ key, result.2 key ≠ none → key ∈ keys := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget cache known result with
  | pure value =>
    rw [compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact ⟨known, by omega, covered⟩
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · rw [compression_run_private] at reached
      obtain ⟨answer, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
      exact ih answer budget (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 answer)
        cache known covered result reached
    · have positive : 1 ≤ budget := bounded.1
      have tails : ∀ answer, PublicQueryBound (next answer) (budget - 1) := bounded.2
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress] at reached
        cases cached : cache input with
        | some answer =>
          rw [cached] at reached
          obtain ⟨keys, size, covers⟩ := ih answer (budget - 1) (tails answer) cache known covered result reached
          exact ⟨keys, by omega, covers⟩
        | none =>
          rw [cached] at reached
          obtain ⟨answer, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
          have nextCovered : ∀ key, (cache.cacheQuery input answer) key ≠ none →
              key ∈ insert input known := by
            intro key populated
            by_cases same : key = input
            · exact same ▸ Finset.mem_insert_self _ _
            · rw [QueryCache.cacheQuery_of_ne _ _ same] at populated
              exact Finset.mem_insert_of_mem (covered key populated)
          obtain ⟨keys, size, covers⟩ := ih answer (budget - 1) (tails answer)
            (cache.cacheQuery input answer) (insert input known) nextCovered result reached
          have inserted := Finset.card_insert_le input known
          exact ⟨keys, by omega, covers⟩
      · rcases permQuery with input | input
        · rw [compression_run_permute] at reached
          obtain ⟨keys, size, covers⟩ := ih _ (budget - 1) (tails _) cache known covered result reached
          exact ⟨keys, by omega, covers⟩
        · rw [compression_run_inverse] at reached
          obtain ⟨keys, size, covers⟩ := ih _ (budget - 1) (tails _) cache known covered result reached
          exact ⟨keys, by omega, covers⟩

theorem first_stage_cache_bound (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) (result : α × CompressionCache)
    (reached : result ∈ support (compressionRun permutation computation ∅)) :
    ∃ keys : Finset CompressionSpec.Domain, keys.card ≤ budget ∧
      ∀ key, result.2 key ≠ none → key ∈ keys := by
  have r := compression_cache_covered permutation computation budget bounded ∅ ∅ (by simp) result reached
  simpa only [Finset.card_empty, Nat.zero_add] using r

theorem staged_observe_query_bound {State Output : Type} {openingSize budget : Nat}
    (permutation : Perm) (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget)
    (result : Hiding.HidingChallenge State openingSize × CompressionCache)
    (reached : result ∈ support (compressionRun permutation adversary.choose ∅))
    (root : Commitment) (proof : Proof) :
    PublicQueryBound (adversary.observe result.1.aux root proof) budget := by
  have projected : result.1 ∈ support
      ((simulateQ (compressionHandler permutation) adversary.choose).run' ∅) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨result, reached, rfl⟩
  have possible := support_simulateQ_run'_subset (compressionHandler permutation) adversary.choose ∅ projected
  have instrumented : result.1 ∈ support (Prod.fst <$> Hiding.counted adversary.choose) := by
    have projection : Prod.fst <$> Hiding.counted adversary.choose = adversary.choose :=
      fst_map_costDist adversary.choose ⟨Oracle.callCost⟩
    rw [projection]
    exact possible
  rw [support_map] at instrumented
  obtain ⟨⟨challenge, calls⟩, counted, equal⟩ := instrumented
  change challenge = result.1 at equal
  subst challenge
  exact (hiding_observe_query_bound adversary bounded (result.1, calls) counted root proof).mono
    (Nat.sub_le _ _)

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

theorem cache_answers_bound (cache : CompressionCache) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) :
    PublicQueryBound (cacheAnswers cache computation) budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure _ => trivial
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩
    · rcases publicQuery with input | permQuery
      · change PublicQueryBound
          (match cache input with
           | some answer => cacheAnswers cache (next answer)
           | none => (liftM (World.query (.inr (.inl input))) : OracleComp World _) >>=
               fun answer => cacheAnswers cache (next answer)) budget
        cases cached : cache input with
        | none => exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩
        | some answer => exact (ih answer _ (bounded.2 answer)).mono (Nat.sub_le _ _)
      · exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩

theorem fixed_cache_answers (cache : CompressionCache) (oracle : Oracle) {α : Type}
    (computation : OracleComp World α) :
    fixedOracleRun oracle (cacheAnswers cache computation) =
      fixedOracleRun ⟨tableExtending cache oracle.compression, oracle.permutation⟩ computation := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
    change fixedOracleRun oracle (pure value) = _
    rw [fixed_oracle_run_pure, fixed_oracle_run_pure]
  | query_bind query next ih =>
    rcases query with coins | publicQuery
    · change fixedOracleRun oracle ((liftM (World.query (.inl coins)) : OracleComp World _) >>=
        fun a => cacheAnswers cache (next a)) = _
      rw [fixed_oracle_run_private, fixed_oracle_run_private]
      exact bind_congr ih
    · rcases publicQuery with input | permQuery
      · change fixedOracleRun oracle
          (match cache input with
           | some answer => cacheAnswers cache (next answer)
           | none => (liftM (World.query (.inr (.inl input))) : OracleComp World _) >>=
               fun a => cacheAnswers cache (next a)) = _
        rw [fixed_oracle_run_public]
        cases cached : cache input with
        | none =>
          rw [fixed_oracle_run_public, ih]
          congr 2; change oracle.compression input = (cache input).getD (oracle.compression input)
          rw [cached]; rfl
        | some answer =>
          rw [ih]
          congr 2; change answer = (cache input).getD (oracle.compression input)
          rw [cached]; rfl
      · change fixedOracleRun oracle ((liftM (World.query (.inr (.inr permQuery))) : OracleComp World _) >>=
          fun a => cacheAnswers cache (next a)) = _
        rw [fixed_oracle_run_public, fixed_oracle_run_public, ih]
        cases permQuery <;> rfl

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

/-! ### 3. 256-bit Chaining-Value Hiding for Leaf Calls 1..3 (Reused in Step 2) -/

private theorem uniform_list_guess (width : Nat) (guesses : List (BitVec width)) :
    (prEvent ((fun value => value ∈ guesses) <$> ($ᵗ BitVec width))) ≤
      (guesses.length : ENNReal) / 2 ^ width := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hsel : (Finset.univ.filter fun value => value ∈ guesses) = guesses.toFinset := by ext v; simp
  have hcard : Fintype.card (BitVec width) = 2 ^ width := Fintype.card_bitVec width
  rw [hsel, hcard]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (List.toFinset_card_le guesses)) _

theorem fresh_trace_hit_256 (trace : List (BitVec COMPRESSION_INPUT_LENGTH)) :
    (prEvent ((fun salt : Digest => trace.any (fun inp => decide (inp.extractLsb' 0 256 = salt)) = true) <$>
      ($ᵗ Digest))) ≤ (trace.length : ENNReal) / 2 ^ 256 := by
  have hev : (fun salt : Digest => trace.any (fun inp => decide (inp.extractLsb' 0 256 = salt)) = true) =
      (fun salt => salt ∈ trace.map (fun inp => inp.extractLsb' 0 256)) := by
    funext salt; simp [List.any_eq_true]
  rw [hev]
  simpa only [List.length_map] using uniform_list_guess 256 (trace.map (fun inp => inp.extractLsb' 0 256))

theorem fresh_query_hit_256 (oracle : Oracle) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) :
    (prEvent ((fun result : α × Unit × Bool => result.2.2 = true) <$>
      (($ᵗ Digest) >>= fun salt => flaggedRun oracle (marksSalt salt) computation))) ≤
      (budget : ENNReal) / 2 ^ 256 := by
  letI : MeasurableSpace (α × Unit × Bool) := ⊤
  have hreord :
      𝒟[($ᵗ Digest) >>= fun salt => flaggedRun oracle (marksSalt salt) computation] =
      𝒟[do let traced ← fixedOracleRun oracle (traceCompression computation)
           let salt ← $ᵗ Digest
           pure (traced.1, (), traced.2.any (fun inp => decide (inp.extractLsb' 0 256 = salt)))] := by
    simp only [flagged_run_trace, Bool.false_or, map_eq_bind_pure_comp]
    exact distribution_bind_comm ($ᵗ Digest) (fixedOracleRun oracle (traceCompression computation)) _
  rw [(EvalDistEq.of_evalDist_eq hreord).prEvent_eq (fun r => r.2.2 = true)]
  apply prEvent_bind_le_of_forall_le_of_support
  intro traced reached
  rw [bind_pure_comp, prEvent_map]
  exact (fresh_trace_hit_256 traced.2).trans
    (ENNReal.div_le_div_right (Nat.cast_le.mpr (trace_run_length oracle computation budget bounded traced reached)) _)

theorem extractLsb'_cast_eq {m n : Nat} (h : m = n) (x : BitVec m) (start len : Nat) :
    (x.cast h).extractLsb' start len = x.extractLsb' start len := by
  subst h; rfl

theorem extractLsb'_0_192_append_digest {m : Nat} (hi : BitVec m) (lo : Digest) :
    (hi ++ lo).extractLsb' 0 192 = lo.extractLsb' 0 192 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.zero_add,
    hb, decide_true, Bool.true_and, show b < 256 by omega, ite_true]

theorem fixed_oracle_run_compress (oracle : Oracle) {α : Type}
    (x : BitVec COMPRESSION_INPUT_LENGTH) (next : Digest → OracleComp World α) :
    fixedOracleRun oracle ((liftM (World.query (.inr (.inl x))) : OracleComp World Digest) >>= next) =
      fixedOracleRun oracle (next (oracle.compression x)) :=
  fixed_oracle_run_public oracle (.inl x) next

def chainInput (h768 : COMPRESSION_INPUT_LENGTH = 768) (cv : Digest) (blk : BitVec 512) :
    BitVec COMPRESSION_INPUT_LENGTH :=
  (blk ++ cv).cast h768.symm

theorem chainInput_cv (h768 : COMPRESSION_INPUT_LENGTH = 768) (cv : Digest) (blk : BitVec 512) :
    (chainInput h768 cv blk).extractLsb' 0 256 = cv := by
  unfold chainInput
  rw [extractLsb'_cast_eq]
  exact BitVec.extractLsb'_append_eq_right

theorem cached_chain_step_distance (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (blk : BitVec 512) {α : Type} (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ ans, PublicQueryBound (next ans) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let cv ← $ᵗ Digest
          let oracle : Oracle := ⟨tableExtending cache table, permutation⟩
          fixedOracleRun oracle (next (oracle.compression (chainInput h768 cv blk))))
      (do let table ← $ᵗ Compression
          let ans ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next ans)) ≤
      ((keys.card + budget : Nat) : ℝ) / 2 ^ 256 := by
  let mid : ProbComp α := do
    let table ← $ᵗ Compression
    let cv ← $ᵗ Digest
    fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next (table (chainInput h768 cv blk)))
  have hprior : measureTVDist
      (do let table ← $ᵗ Compression
          let cv ← $ᵗ Digest
          let oracle : Oracle := ⟨tableExtending cache table, permutation⟩
          fixedOracleRun oracle (next (oracle.compression (chainInput h768 cv blk))))
      mid ≤ ((keys.card : ENNReal) / 2 ^ 256).toReal := by
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression) _ _ (by positivity)
    intro table
    refine (measureTVDist_bind_left_le_prEvent_of_evalDistEq ($ᵗ Digest) _ _
      (fun cv => cache (chainInput h768 cv blk) ≠ none) ?_).trans ?_
    · intro cv hnone
      have hempty : cache (chainInput h768 cv blk) = none := Classical.not_not.mp hnone
      have hsame : tableExtending cache table (chainInput h768 cv blk) = table (chainInput h768 cv blk) := by
        change (cache (chainInput h768 cv blk)).getD (table (chainInput h768 cv blk)) = _
        rw [hempty]; rfl
      dsimp only; rw [hsame]
    · have hinc : (prEvent ((fun cv : Digest => cache (chainInput h768 cv blk) ≠ none) <$> ($ᵗ Digest))) ≤
          (prEvent ((fun cv : Digest => keys.toList.any (fun inp => decide (inp.extractLsb' 0 256 = cv)) = true) <$> ($ᵗ Digest))) := by
        apply prEvent_mono_of_support
        intro cv _ hit
        exact List.any_eq_true.mpr ⟨chainInput h768 cv blk, Finset.mem_toList.mpr (covered _ hit),
          decide_eq_true (chainInput_cv h768 cv blk)⟩
      exact ENNReal.toReal_mono (by finiteness)
        (hinc.trans (by simpa only [Finset.length_toList] using fresh_trace_hit_256 keys.toList))
  have hafter : measureTVDist mid
      (do let table ← $ᵗ Compression
          let ans ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next ans)) ≤
      ((budget : ENNReal) / 2 ^ 256).toReal := by
    let next' : Digest → OracleComp World α := fun ans => cacheAnswers cache (next ans)
    have hbd' : ∀ ans, PublicQueryBound (next' ans) budget :=
      fun ans => cache_answers_bound cache (next ans) budget (bounded ans)
    let ideal : ProbComp α := do
      let ans ← $ᵗ Digest
      let table ← $ᵗ Compression
      let _cv ← $ᵗ Digest
      fixedOracleRun ⟨table, permutation⟩ (next' ans)
    let prog : ProbComp α := do
      let ans ← $ᵗ Digest
      let table ← $ᵗ Compression
      let cv ← $ᵗ Digest
      fixedOracleRun (programCompression ⟨table, permutation⟩ (chainInput h768 cv blk) ans) (next' ans)
    have hdist : measureTVDist ideal prog ≤ ((budget : ENNReal) / 2 ^ 256).toReal := by
      apply measureTVDist_bind_left_le_of_forall_le ($ᵗ Digest) _ _ (by positivity)
      intro ans
      apply measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression) _ _ (by positivity)
      intro table
      have havg := distance_bind_le_averaged_bad ($ᵗ Digest)
        (fun _ => fixedOracleRun ⟨table, permutation⟩ (next' ans))
        (fun cv => fixedOracleRun (programCompression ⟨table, permutation⟩ (chainInput h768 cv blk) ans) (next' ans))
        (fun cv => flaggedRun ⟨table, permutation⟩ (marksSalt cv) (next' ans))
        (fun cv => by
          have hr := reprogram_compression_distance ⟨table, permutation⟩ (chainInput h768 cv blk) ans (next' ans)
          rwa [chainInput_cv h768 cv blk] at hr)
      exact havg.trans (ENNReal.toReal_mono (by finiteness)
        (fresh_query_hit_256 ⟨table, permutation⟩ (next' ans) budget (hbd' ans)))
    have hideal : 𝒟[ideal] = 𝒟[do let table ← $ᵗ Compression
                                  let ans ← $ᵗ Digest
                                  fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next ans)] := by
      unfold ideal
      trans 𝒟[do let ans ← $ᵗ Digest
                 let table ← $ᵗ Compression
                 fixedOracleRun ⟨table, permutation⟩ (next' ans)]
      · apply _root_.evalDist_bind_congr; intro ans
        apply _root_.evalDist_bind_congr; intro table
        exact OracleComp.evalDist_bind_const _ _
      · rw [distribution_bind_comm]
        apply _root_.evalDist_bind_congr; intro table
        apply _root_.evalDist_bind_congr; intro ans
        rw [fixed_cache_answers]
    have hprog : 𝒟[prog] = 𝒟[mid] := by
      unfold prog mid
      trans 𝒟[do let cv ← $ᵗ Digest
                 let ans ← $ᵗ Digest
                 let table ← $ᵗ Compression
                 fixedOracleRun (programCompression ⟨table, permutation⟩ (chainInput h768 cv blk) ans) (next' ans)]
      · trans 𝒟[do let ans ← $ᵗ Digest
                   let cv ← $ᵗ Digest
                   let table ← $ᵗ Compression
                   fixedOracleRun (programCompression ⟨table, permutation⟩ (chainInput h768 cv blk) ans) (next' ans)]
        · exact _root_.evalDist_bind_congr _ _ _ (fun _ => distribution_bind_comm _ _ _)
        · exact distribution_bind_comm _ _ _
      · trans 𝒟[do let cv ← $ᵗ Digest
                   let table ← $ᵗ Compression
                   fixedOracleRun ⟨table, permutation⟩ (next' (table (chainInput h768 cv blk)))]
        · apply _root_.evalDist_bind_congr; intro cv
          trans 𝒟[do let ans ← $ᵗ Digest
                     let table ← $ᵗ Compression
                     fixedOracleRun ⟨Function.update table (chainInput h768 cv blk) ans, permutation⟩
                       (next' ((Function.update table (chainInput h768 cv blk) ans) (chainInput h768 cv blk)))]
          · apply _root_.evalDist_bind_congr; intro ans
            apply _root_.evalDist_bind_congr; intro table
            erw [Function.update_self]; rfl
          · exact compression_table_update_bind (chainInput h768 cv blk)
              (fun table => fixedOracleRun ⟨table, permutation⟩ (next' (table (chainInput h768 cv blk))))
        · rw [distribution_bind_comm]
          apply _root_.evalDist_bind_congr; intro table
          apply _root_.evalDist_bind_congr; intro cv
          rw [fixed_cache_answers]
    rw [measureTVDist_comm] at hdist
    simpa only [measureTVDist, hideal, hprog] using hdist
  refine ((measureTVDist_triangle _ mid _).trans (add_le_add hprior hafter)).trans ?_
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat, Nat.cast_add]
  exact le_of_eq (add_div _ _ _).symm

def queryChain3 (h768 : COMPRESSION_INPUT_LENGTH = 768) (val : Entry) (cv0 : Digest) :
    OracleComp World Digest := do
  let cv1 ← (liftM (World.query (.inr (.inl (chainInput h768 cv0 (val.extractLsb' 576 512))))) : OracleComp World Digest)
  let cv2 ← (liftM (World.query (.inr (.inl (chainInput h768 cv1 (val.extractLsb' 1088 512))))) : OracleComp World Digest)
  (liftM (World.query (.inr (.inl (chainInput h768 cv2 (val.extractLsb' 1536 512))))) : OracleComp World Digest)

/-- 3-call leaf chain starting from a fresh 256-bit `cv0`: indistinguishable from a fresh digest
up to `3 * (keys.card + budget + 3) / 2^256`. -/
theorem cached_chain3_distance (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (val : Entry) {α : Type} (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ ans, PublicQueryBound (next ans) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let cv0 ← $ᵗ Digest
          let c : Comp96 := fun x => tableExtending cache table (x.cast h768.symm)
          fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next (leafChainFromCv0 c cv0 val)))
      (do let table ← $ᵗ Compression
          let ans ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next ans)) ≤
      3 * ((keys.card + budget + 3 : Nat) : ℝ) / 2 ^ 256 := by
  let q23 : Digest → OracleComp World α := fun cv1 => do
    let cv2 ← (liftM (World.query (.inr (.inl (chainInput h768 cv1 (val.extractLsb' 1088 512))))) : OracleComp World Digest)
    let cv3 ← (liftM (World.query (.inr (.inl (chainInput h768 cv2 (val.extractLsb' 1536 512))))) : OracleComp World Digest)
    next cv3
  let q3 : Digest → OracleComp World α := fun cv2 => do
    let cv3 ← (liftM (World.query (.inr (.inl (chainInput h768 cv2 (val.extractLsb' 1536 512))))) : OracleComp World Digest)
    next cv3
  have hq3_bd : ∀ cv2, PublicQueryBound (q3 cv2) (budget + 1) := fun cv2 =>
    ⟨by change 1 ≤ budget + 1; omega, fun ans => by
      change PublicQueryBound (next ans) (budget + 1 - 1)
      simpa only [Nat.add_sub_cancel] using bounded ans⟩
  have hq23_bd : ∀ cv1, PublicQueryBound (q23 cv1) (budget + 2) := fun cv1 =>
    ⟨by change 1 ≤ budget + 2; omega, fun ans => by
      change PublicQueryBound (q3 ans) (budget + 2 - 1)
      rw [show budget + 2 - 1 = budget + 1 by omega]
      exact hq3_bd ans⟩
  have h1 := cached_chain_step_distance h768 permutation cache keys covered (val.extractLsb' 576 512) q23 (budget + 2) hq23_bd
  have h2 := cached_chain_step_distance h768 permutation cache keys covered (val.extractLsb' 1088 512) q3 (budget + 1) hq3_bd
  have h3 := cached_chain_step_distance h768 permutation cache keys covered (val.extractLsb' 1536 512) next budget bounded
  have h1' : ∀ (o : Oracle) (cv0 : Digest),
      fixedOracleRun o (q23 (o.compression (chainInput h768 cv0 (val.extractLsb' 576 512)))) =
      fixedOracleRun o (next (leafChainFromCv0 (fun x => o.compression (x.cast h768.symm)) cv0 val)) := by
    intro o cv0
    change fixedOracleRun o ((liftM (World.query (.inr (.inl _))) : OracleComp World Digest) >>= _) = _
    rw [fixed_oracle_run_compress]
    change fixedOracleRun o ((liftM (World.query (.inr (.inl _))) : OracleComp World Digest) >>= _) = _
    rw [fixed_oracle_run_compress]
    rfl
  have h2' : ∀ (o : Oracle) (cv1 : Digest),
      fixedOracleRun o (q23 cv1) =
      fixedOracleRun o (q3 (o.compression (chainInput h768 cv1 (val.extractLsb' 1088 512)))) :=
    fun o cv1 => fixed_oracle_run_compress o _ _
  have h3' : ∀ (o : Oracle) (cv2 : Digest),
      fixedOracleRun o (q3 cv2) =
      fixedOracleRun o (next (o.compression (chainInput h768 cv2 (val.extractLsb' 1536 512)))) :=
    fun o cv2 => fixed_oracle_run_compress o _ _
  let P0 : ProbComp α := do
    let table ← $ᵗ Compression
    let cv0 ← $ᵗ Digest
    let c : Comp96 := fun x => tableExtending cache table (x.cast h768.symm)
    fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next (leafChainFromCv0 c cv0 val))
  let P1 : ProbComp α := do
    let table ← $ᵗ Compression
    let cv1 ← $ᵗ Digest
    let o : Oracle := ⟨tableExtending cache table, permutation⟩
    fixedOracleRun o (q3 (o.compression (chainInput h768 cv1 (val.extractLsb' 1088 512))))
  let P2 : ProbComp α := do
    let table ← $ᵗ Compression
    let cv2 ← $ᵗ Digest
    fixedOracleRun ⟨tableExtending cache table, permutation⟩ (q3 cv2)
  let P3 : ProbComp α := do
    let table ← $ᵗ Compression
    let ans ← $ᵗ Digest
    fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next ans)
  have hP0 : (do let table ← $ᵗ Compression
                 let cv ← $ᵗ Digest
                 let oracle : Oracle := ⟨tableExtending cache table, permutation⟩
                 fixedOracleRun oracle (q23 (oracle.compression (chainInput h768 cv (val.extractLsb' 576 512))))) = P0 := by
    apply bind_congr; intro table
    apply bind_congr; intro cv
    exact h1' ⟨tableExtending cache table, permutation⟩ cv
  have hP1 : (do let table ← $ᵗ Compression
                 let ans ← $ᵗ Digest
                 fixedOracleRun ⟨tableExtending cache table, permutation⟩ (q23 ans)) = P1 := by
    apply bind_congr; intro table
    apply bind_congr; intro ans
    exact h2' ⟨tableExtending cache table, permutation⟩ ans
  have hP2 : P2 = (do let table ← $ᵗ Compression
                      let cv ← $ᵗ Digest
                      let oracle : Oracle := ⟨tableExtending cache table, permutation⟩
                      fixedOracleRun oracle (next (oracle.compression (chainInput h768 cv (val.extractLsb' 1536 512))))) := by
    apply bind_congr; intro table
    apply bind_congr; intro cv
    exact h3' ⟨tableExtending cache table, permutation⟩ cv
  rw [hP0, hP1] at h1
  rw [← hP2] at h3
  have htri1 := (measureTVDist_triangle P0 P1 P2).trans (add_le_add h1 h2)
  have htri2 := (measureTVDist_triangle P0 P2 P3).trans (add_le_add htri1 h3)
  refine htri2.trans ?_
  rw [← add_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) keys.card, Nat.cast_nonneg (α := ℝ) budget]

/-! ### 4. Lazy-ROM `CacheHitsPrefix` Bound (for 192-bit Tag+Salt Prefixes) -/

def CacheHitsPrefix (cache : CompressionCache) (prefixes : Finset (BitVec 192)) : Prop :=
  ∃ (k : BitVec COMPRESSION_INPUT_LENGTH) (ans : Digest),
    cache k = some ans ∧ ans.extractLsb' 0 192 ∈ prefixes

private theorem card_prefix192_preimage (prefixes : Finset (BitVec 192))
    [DecidablePred (fun ans : Digest => ans.extractLsb' 0 192 ∈ prefixes)] :
    (Finset.univ.filter (fun ans : Digest => ans.extractLsb' 0 192 ∈ prefixes)).card ≤
      2 ^ 64 * prefixes.card := by
  have hinj : Set.InjOn (fun ans : Digest => (ans.extractLsb' 192 64, ans.extractLsb' 0 192))
      (Finset.univ.filter (fun ans : Digest => ans.extractLsb' 0 192 ∈ prefixes) : Set Digest) := by
    intro a _ b _ h
    have hhi : a.extractLsb' 192 64 = b.extractLsb' 192 64 := congrArg Prod.fst h
    have hlo : a.extractLsb' 0 192 = b.extractLsb' 0 192 := congrArg Prod.snd h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases h192 : i < 192
    · have := congrArg (fun v : BitVec 192 => v.getLsbD i) hlo
      simpa only [BitVec.getLsbD_extractLsb', h192, decide_true, Bool.true_and, Nat.zero_add] using this
    · have hi64 : i - 192 < 64 := by omega
      have := congrArg (fun v : BitVec 64 => v.getLsbD (i - 192)) hhi
      simpa only [BitVec.getLsbD_extractLsb', hi64, decide_true, Bool.true_and,
        show 192 + (i - 192) = i by omega] using this
  have hmaps : Set.MapsTo (fun ans : Digest => (ans.extractLsb' 192 64, ans.extractLsb' 0 192))
      (Finset.univ.filter (fun ans : Digest => ans.extractLsb' 0 192 ∈ prefixes) : Set Digest)
      ((Finset.univ ×ˢ prefixes : Finset (BitVec 64 × BitVec 192)) : Set (BitVec 64 × BitVec 192)) := by
    intro ans hans
    rw [Finset.mem_coe, Finset.mem_filter] at hans
    rw [Finset.mem_coe, Finset.mem_product]
    exact ⟨Finset.mem_univ _, hans.2⟩
  calc
    (Finset.univ.filter (fun ans : Digest => ans.extractLsb' 0 192 ∈ prefixes)).card
      ≤ (Finset.univ ×ˢ prefixes : Finset (BitVec 64 × BitVec 192)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (Finset.univ : Finset (BitVec 64)).card * prefixes.card := Finset.card_product _ _
    _ = 2 ^ 64 * prefixes.card := by rw [Finset.card_univ, Fintype.card_bitVec]

theorem uniform_digest_hits_prefix_le (prefixes : Finset (BitVec 192)) :
    (prEvent ((fun ans : Digest => ans.extractLsb' 0 192 ∈ prefixes) <$> ($ᵗ Digest))) ≤
      (prefixes.card : ENNReal) / 2 ^ 192 := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hcard : Fintype.card Digest = 2 ^ 256 := Fintype.card_bitVec 256
  rw [hcard]
  calc
    ((Finset.univ.filter (fun ans : Digest => ans.extractLsb' 0 192 ∈ prefixes)).card : ENNReal) / (2 ^ 256 : Nat)
      ≤ ((2 ^ 64 * prefixes.card : Nat) : ENNReal) / (2 ^ 256 : Nat) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr (card_prefix192_preimage prefixes)) _
    _ = (prefixes.card : ENNReal) / 2 ^ 192 := by
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [show (2 : ENNReal) ^ 256 = 2 ^ 64 * 2 ^ 192 by rw [← pow_add]]
        exact ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)

theorem compression_run_hits_prefix_bound (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget)
    (cache : CompressionCache) (prefixes : Finset (BitVec 192))
    (hclean : ¬ CacheHitsPrefix cache prefixes) :
    (prEvent ((fun res => CacheHitsPrefix res.2 prefixes) <$> (compressionRun permutation computation cache))) ≤
      (budget : ENNReal) * ((prefixes.card : ENNReal) / 2 ^ 192) := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget cache with
  | pure value =>
    rw [compression_run_pure]
    simp only [prEvent_pure, hclean, ite_false]
    exact zero_le
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ ans, PublicQueryBound (next ans) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · rw [compression_run_private]
      apply prEvent_bind_le_of_forall_le_of_support
      intro ans _
      exact ih ans budget (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 ans) cache hclean
    · have hpos : 1 ≤ budget := bounded.1
      have htails := bounded.2
      have hmono : ((budget - 1 : Nat) : ENNReal) * ((prefixes.card : ENNReal) / 2 ^ 192) ≤
          (budget : ENNReal) * ((prefixes.card : ENNReal) / 2 ^ 192) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le budget 1)) zero_le
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress]
        cases hcached : cache input with
        | some ans =>
          exact (ih ans (budget - 1) (htails ans) cache hclean).trans hmono
        | none =>
          have hfresh : (prEvent ((fun ans : Digest => CacheHitsPrefix (cache.cacheQuery input ans) prefixes) <$>
              ($ᵗ CompressionSpec.Range input))) ≤ (prefixes.card : ENNReal) / 2 ^ 192 := by
            have hle : (prEvent ((fun ans : Digest => CacheHitsPrefix (cache.cacheQuery input ans) prefixes) <$>
                ($ᵗ CompressionSpec.Range input))) ≤
                (prEvent ((fun ans : Digest => ans.extractLsb' 0 192 ∈ prefixes) <$> ($ᵗ Digest))) := by
              apply prEvent_mono_of_support
              intro ans _ ⟨k, v, hkv, hmem⟩
              by_cases hk : k = input
              · subst hk
                erw [QueryCache.cacheQuery_self cache k ans] at hkv
                cases hkv
                exact hmem
              · erw [QueryCache.cacheQuery_of_ne cache ans hk] at hkv
                exact (hclean ⟨k, v, hkv, hmem⟩).elim
            exact hle.trans (uniform_digest_hits_prefix_le prefixes)
          have hcont : ∀ ans ∈ support ($ᵗ CompressionSpec.Range input),
              ¬ CacheHitsPrefix (cache.cacheQuery input ans) prefixes →
              (prEvent ((fun res => CacheHitsPrefix res.2 prefixes) <$>
                (compressionRun permutation (next ans) (cache.cacheQuery input ans)))) ≤
                ((budget - 1 : Nat) : ENNReal) * ((prefixes.card : ENNReal) / 2 ^ 192) :=
            fun ans _ hsafe => ih ans (budget - 1) (htails ans) _ hsafe
          have hcomb := (prEvent_bind_le_prEvent_add_of_support
            ($ᵗ CompressionSpec.Range input)
            (fun ans => compressionRun permutation (next ans) (cache.cacheQuery input ans))
            (fun ans => CacheHitsPrefix (cache.cacheQuery input ans) prefixes)
            (fun res => CacheHitsPrefix res.2 prefixes) hcont).trans (add_le_add hfresh le_rfl)
          apply hcomb.trans_eq
          conv_rhs => rw [show budget = 1 + (budget - 1) by omega]
          push_cast; ring
      · rcases permQuery with input | input
        · rw [compression_run_permute]; exact (ih _ (budget - 1) (htails _) cache hclean).trans hmono
        · rw [compression_run_inverse]; exact (ih _ (budget - 1) (htails _) cache hclean).trans hmono

/-! ### 5. Bottom-Up Oracle Evaluation of the r=1 Tree (`<= 78,293,674` Queries) -/

def HONEST_TREE_BUDGET : Nat := 4 * LENGTH + 11184810

theorem public_query_bound_pure' {α : Type} (x : α) (n : Nat) :
    PublicQueryBound (pure x : OracleComp World α) n := trivial

private def queryCompress (h768 : COMPRESSION_INPUT_LENGTH = 768) (x : BitVec 768) :
    OracleComp World Digest :=
  (liftM (World.query (.inr (.inl (x.cast h768.symm)))) : OracleComp World Digest)

theorem queryCompress_bound (h768 : COMPRESSION_INPUT_LENGTH = 768) (x : BitVec 768) :
    PublicQueryBound (queryCompress h768 x) 1 :=
  ⟨Nat.le_refl 1, fun ans => public_query_bound_pure' (α := Digest) ans 0⟩

def oracleComp96 (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle) : Comp96 :=
  fun x => oracle.compression (x.cast h768.symm)

theorem queryCompress_fixed (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle) (x : BitVec 768) :
    fixedOracleRun oracle (queryCompress h768 x) = pure (oracleComp96 h768 oracle x) := by
  unfold queryCompress
  change fixedOracleRun oracle ((liftM (World.query (.inr (.inl (x.cast h768.symm)))) : OracleComp World Digest) >>= (pure : Digest → OracleComp World Digest)) = _
  rw [fixed_oracle_run_compress]
  exact fixed_oracle_run_pure oracle (α := Digest) (oracleComp96 h768 oracle x)

def queryLeafOpened (h768 : COMPRESSION_INPUT_LENGTH = 768) (i : Index) (salt : Salt128) (val : Entry) :
    OracleComp World Digest := do
  let cv0 ← queryCompress h768 (leafCall0Input i salt val)
  let cv1 ← queryCompress h768 (leafCall1Input cv0 val)
  let cv2 ← queryCompress h768 (leafCall2Input cv1 val)
  queryCompress h768 (leafCall3Input cv2 val)

def queryLeafFromCv0 (h768 : COMPRESSION_INPUT_LENGTH = 768) (cv0 : Digest) (val : Entry) :
    OracleComp World Digest := do
  let cv1 ← queryCompress h768 (leafCall1Input cv0 val)
  let cv2 ← queryCompress h768 (leafCall2Input cv1 val)
  queryCompress h768 (leafCall3Input cv2 val)

theorem queryLeafOpened_fixed (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (i : Index) (salt : Salt128) (val : Entry) :
    fixedOracleRun oracle (queryLeafOpened h768 i salt val) =
      pure (leafDigest (oracleComp96 h768 oracle) i salt val) := by
  unfold queryLeafOpened leafDigest leafChainFromCv0
  simp only [fixed_oracle_run_bind, queryCompress_fixed, pure_bind]

theorem queryLeafFromCv0_fixed (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (cv0 : Digest) (val : Entry) :
    fixedOracleRun oracle (queryLeafFromCv0 h768 cv0 val) =
      pure (leafChainFromCv0 (oracleComp96 h768 oracle) cv0 val) := by
  unfold queryLeafFromCv0 leafChainFromCv0
  simp only [fixed_oracle_run_bind, queryCompress_fixed, pure_bind]

theorem queryLeafOpened_bound (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (i : Index) (salt : Salt128) (val : Entry) :
    PublicQueryBound (queryLeafOpened h768 i salt val) 4 := by
  unfold queryLeafOpened
  exact public_query_bound_bind (first := 1) (second := 3) (queryCompress_bound h768 _) fun _ =>
    public_query_bound_bind (first := 1) (second := 2) (queryCompress_bound h768 _) fun _ =>
      public_query_bound_bind (first := 1) (second := 1) (queryCompress_bound h768 _) fun _ =>
        queryCompress_bound h768 _

theorem queryLeafFromCv0_bound (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (cv0 : Digest) (val : Entry) :
    PublicQueryBound (queryLeafFromCv0 h768 cv0 val) 3 := by
  unfold queryLeafFromCv0
  exact public_query_bound_bind (first := 1) (second := 2) (queryCompress_bound h768 _) fun _ =>
    public_query_bound_bind (first := 1) (second := 1) (queryCompress_bound h768 _) fun _ =>
      queryCompress_bound h768 _

def queryLevel0Aux (leafFn : Index → OracleComp World Digest) : Nat → OracleComp World (Nat → Digest)
  | 0 => pure (fun _ => 0)
  | n + 1 => do
      let prev ← queryLevel0Aux leafFn n
      if h : n < LENGTH then
        let d ← leafFn ⟨n, h⟩
        pure (Function.update prev n d)
      else pure prev

def queryLevel1Aux (h768 : COMPRESSION_INPUT_LENGTH = 768) (l0 : Nat → Digest) :
    Nat → OracleComp World (Nat → Digest)
  | 0 => pure (fun idx => if idx = FULL_TRIPLETS then l0 (3 * FULL_TRIPLETS) else 0)
  | n + 1 => do
      let prev ← queryLevel1Aux h768 l0 n
      let d ← queryCompress h768 (ternaryInput (l0 (3 * n)) (l0 (3 * n + 1)) (l0 (3 * n + 2)))
      pure (Function.update prev n d)

def queryBinLevelAux (h768 : COMPRESSION_INPUT_LENGTH = 768) (prevLevel : Nat → Digest)
    (prevSize : Nat) (isRoot : Bool) : Nat → OracleComp World (Nat → Digest)
  | 0 => pure (fun idx =>
      if prevSize % 2 = 1 ∧ idx = prevSize / 2 then prevLevel (2 * idx) else 0)
  | n + 1 => do
      let prev ← queryBinLevelAux h768 prevLevel prevSize isRoot n
      let raw ← queryCompress h768 (binaryInput (prevLevel (2 * n)) (prevLevel (2 * n + 1)))
      let d := if isRoot then raw else mask240 raw
      pure (Function.update prev n d)

def queryUpperLevels (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (l0 l1 : Nat → Digest) : Nat → OracleComp World (Nat → Nat → Digest)
  | 0 => pure (fun l idx => if l = 0 then l0 idx else if l = 1 then l1 idx else 0)
  | k + 1 => do
      let prev ← queryUpperLevels h768 l0 l1 k
      let prevLvl := k + 1
      let cur ← queryBinLevelAux h768 (prev prevLvl) (levelSize prevLvl) (decide (k + 2 = 24)) (levelSize prevLvl / 2)
      pure (Function.update prev (k + 2) cur)

def queryTreeFromLeafFn (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (leafFn : Index → OracleComp World Digest) : OracleComp World (Nat → Nat → Digest) := do
  let l0 ← queryLevel0Aux leafFn LENGTH
  let l1 ← queryLevel1Aux h768 l0 FULL_TRIPLETS
  queryUpperLevels h768 l0 l1 23

private theorem queryLevel0Aux_zero (leafFn : Index → OracleComp World Digest) :
    queryLevel0Aux leafFn 0 = pure (fun _ => 0) := rfl

private theorem queryLevel0Aux_succ (leafFn : Index → OracleComp World Digest) (n : Nat) :
    queryLevel0Aux leafFn (n + 1) = (do
      let prev ← queryLevel0Aux leafFn n
      if h : n < LENGTH then
        let d ← leafFn ⟨n, h⟩
        pure (Function.update prev n d)
      else pure prev) := rfl

private theorem queryLevel1Aux_zero (h768 : COMPRESSION_INPUT_LENGTH = 768) (l0 : Nat → Digest) :
    queryLevel1Aux h768 l0 0 = pure (fun idx => if idx = FULL_TRIPLETS then l0 (3 * FULL_TRIPLETS) else 0) := rfl

private theorem queryLevel1Aux_succ (h768 : COMPRESSION_INPUT_LENGTH = 768) (l0 : Nat → Digest) (n : Nat) :
    queryLevel1Aux h768 l0 (n + 1) = (do
      let prev ← queryLevel1Aux h768 l0 n
      let d ← queryCompress h768 (ternaryInput (l0 (3 * n)) (l0 (3 * n + 1)) (l0 (3 * n + 2)))
      pure (Function.update prev n d)) := rfl

private theorem queryBinLevelAux_zero (h768 : COMPRESSION_INPUT_LENGTH = 768) (prevLevel : Nat → Digest)
    (prevSize : Nat) (isRoot : Bool) :
    queryBinLevelAux h768 prevLevel prevSize isRoot 0 =
      pure (fun idx => if prevSize % 2 = 1 ∧ idx = prevSize / 2 then prevLevel (2 * idx) else 0) := rfl

private theorem queryBinLevelAux_succ (h768 : COMPRESSION_INPUT_LENGTH = 768) (prevLevel : Nat → Digest)
    (prevSize : Nat) (isRoot : Bool) (n : Nat) :
    queryBinLevelAux h768 prevLevel prevSize isRoot (n + 1) = (do
      let prev ← queryBinLevelAux h768 prevLevel prevSize isRoot n
      let raw ← queryCompress h768 (binaryInput (prevLevel (2 * n)) (prevLevel (2 * n + 1)))
      let d := if isRoot then raw else mask240 raw
      pure (Function.update prev n d)) := rfl

private theorem queryUpperLevels_zero (h768 : COMPRESSION_INPUT_LENGTH = 768) (l0 l1 : Nat → Digest) :
    queryUpperLevels h768 l0 l1 0 = pure (fun l idx => if l = 0 then l0 idx else if l = 1 then l1 idx else 0) := rfl

private theorem queryUpperLevels_succ (h768 : COMPRESSION_INPUT_LENGTH = 768) (l0 l1 : Nat → Digest) (k : Nat) :
    queryUpperLevels h768 l0 l1 (k + 1) = (do
      let prev ← queryUpperLevels h768 l0 l1 k
      let prevLvl := k + 1
      let cur ← queryBinLevelAux h768 (prev prevLvl) (levelSize prevLvl) (decide (k + 2 = 24)) (levelSize prevLvl / 2)
      pure (Function.update prev (k + 2) cur)) := rfl

private theorem queryTreeFromLeafFn_def (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (leafFn : Index → OracleComp World Digest) :
    queryTreeFromLeafFn h768 leafFn = (do
      let l0 ← queryLevel0Aux leafFn LENGTH
      let l1 ← queryLevel1Aux h768 l0 FULL_TRIPLETS
      queryUpperLevels h768 l0 l1 23) := rfl

attribute [irreducible] queryLevel0Aux queryLevel1Aux queryBinLevelAux queryUpperLevels queryTreeFromLeafFn

private theorem sum_bin_calls_eq :
    (∑ k ∈ Finset.range 23, levelSize (k + 1) / 2) = 5592405 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [levelSize, LENGTH, LOG_LENGTH]

theorem queryTreeFromLeafFn_bound (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (leafFn : Index → OracleComp World Digest)
    (hleaf : ∀ i, PublicQueryBound (leafFn i) 4) :
    PublicQueryBound (queryTreeFromLeafFn h768 leafFn) HONEST_TREE_BUDGET := by
  have hl0 : ∀ n, PublicQueryBound (queryLevel0Aux leafFn n) (4 * n) := by
    intro n; induction n with
    | zero => rw [queryLevel0Aux_zero]; exact public_query_bound_pure' _ _
    | succ n ih =>
      rw [queryLevel0Aux_succ, show 4 * (n + 1) = 4 * n + 4 by omega]
      apply public_query_bound_bind ih
      intro prev
      split
      · simpa only [Nat.add_zero] using public_query_bound_bind (hleaf _) (fun _ => public_query_bound_pure' _ 0)
      · exact (public_query_bound_pure' prev 0).mono (by omega)
  have hl1 : ∀ l0 n, PublicQueryBound (queryLevel1Aux h768 l0 n) n := by
    intro l0 n; induction n with
    | zero => rw [queryLevel1Aux_zero]; exact public_query_bound_pure' _ _
    | succ n ih =>
      rw [queryLevel1Aux_succ]
      apply public_query_bound_bind ih
      intro _
      simpa only [Nat.add_zero] using public_query_bound_bind (queryCompress_bound h768 _) (fun _ => public_query_bound_pure' _ 0)
  have hbin : ∀ pl ps ir n, PublicQueryBound (queryBinLevelAux h768 pl ps ir n) n := by
    intro pl ps ir n; induction n with
    | zero => rw [queryBinLevelAux_zero]; exact public_query_bound_pure' _ _
    | succ n ih =>
      rw [queryBinLevelAux_succ]
      apply public_query_bound_bind ih
      intro _
      simpa only [Nat.add_zero] using public_query_bound_bind (queryCompress_bound h768 _) (fun _ => public_query_bound_pure' _ 0)
  have hup : ∀ l0 l1 k, PublicQueryBound (queryUpperLevels h768 l0 l1 k) (∑ j ∈ Finset.range k, levelSize (j + 1) / 2) := by
    intro l0 l1 k; induction k with
    | zero =>
      rw [queryUpperLevels_zero]
      simp only [Finset.range_zero, Finset.sum_empty]
      exact public_query_bound_pure' _ _
    | succ k ih =>
      rw [queryUpperLevels_succ, Finset.sum_range_succ]
      apply public_query_bound_bind ih
      intro prev
      simpa only [Nat.add_zero] using public_query_bound_bind (hbin _ _ _ _) (fun _ => public_query_bound_pure' _ 0)
  rw [queryTreeFromLeafFn_def]
  have hbudget : HONEST_TREE_BUDGET = 4 * LENGTH + (FULL_TRIPLETS + 5592405) := by
    unfold HONEST_TREE_BUDGET; rw [full_triplets_eq]
  rw [hbudget]
  refine public_query_bound_bind (hl0 LENGTH) fun l0 =>
    public_query_bound_bind (hl1 l0 FULL_TRIPLETS) fun l1 => ?_
  rw [← sum_bin_calls_eq]
  exact hup l0 l1 23

theorem queryTreeFromLeafFn_fixed (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (leafFn : Index → OracleComp World Digest) (leaves : Index → Digest)
    (hleaf : ∀ i, fixedOracleRun oracle (leafFn i) = pure (leaves i)) :
    ∃ nodes,
      fixedOracleRun oracle (queryTreeFromLeafFn h768 leafFn) = pure nodes ∧
      ∀ l ≤ 24, ∀ idx < levelSize l,
        nodes l idx = nodeValFromLeaves (fun x => oracle.compression (x.cast h768.symm)) leaves l idx := by
  let c : Comp96 := oracleComp96 h768 oracle
  have hl0 : ∀ n, ∃ f, fixedOracleRun oracle (queryLevel0Aux leafFn n) = pure f ∧
      ∀ idx < n, idx < LENGTH → f idx = nodeValFromLeaves c leaves 0 idx := by
    intro n; induction n with
    | zero =>
      rw [queryLevel0Aux_zero]
      exact ⟨fun _ => 0, fixed_oracle_run_pure _ _, fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ n ih =>
      obtain ⟨f, hrun, hval⟩ := ih
      rw [queryLevel0Aux_succ, fixed_oracle_run_bind, hrun, pure_bind]
      by_cases hn : n < LENGTH
      · rw [dif_pos hn, fixed_oracle_run_bind, hleaf ⟨n, hn⟩, pure_bind, fixed_oracle_run_pure]
        refine ⟨Function.update f n (leaves ⟨n, hn⟩), rfl, ?_⟩
        intro idx hlt hlen
        by_cases heq : idx = n
        · subst heq; simp [nodeValFromLeaves, hn]
        · rw [Function.update_of_ne heq]; exact hval idx (by omega) hlen
      · rw [dif_neg hn, fixed_oracle_run_pure]
        exact ⟨f, rfl, fun idx hlt hlen => hval idx (by omega) hlen⟩
  obtain ⟨l0, hl0_run, hl0_val⟩ := hl0 LENGTH
  have hl0_all : ∀ idx < levelSize 0, l0 idx = nodeValFromLeaves c leaves 0 idx :=
    fun idx h => hl0_val idx (by rwa [levelSize_0, show (16777216 : Nat) = LENGTH by decide] at h)
      (by rwa [levelSize_0, show (16777216 : Nat) = LENGTH by decide] at h)
  have hl1 : ∀ n, n ≤ FULL_TRIPLETS → ∃ f, fixedOracleRun oracle (queryLevel1Aux h768 l0 n) = pure f ∧
      (∀ idx < n, f idx = nodeValFromLeaves c leaves 1 idx) ∧
      f FULL_TRIPLETS = nodeValFromLeaves c leaves 1 FULL_TRIPLETS := by
    intro n hn; induction n with
    | zero =>
      rw [queryLevel1Aux_zero]
      refine ⟨_, fixed_oracle_run_pure _ _, fun _ h => (Nat.not_lt_zero _ h).elim, ?_⟩
      simp only [ite_true, nodeValFromLeaves, lt_irrefl, ite_false]
      exact hl0_all (3 * FULL_TRIPLETS) (by rw [levelSize_0, full_triplets_eq]; omega)
    | succ n ih =>
      obtain ⟨f, hrun, hval, hprom⟩ := ih (by omega)
      rw [queryLevel1Aux_succ, fixed_oracle_run_bind, hrun, pure_bind, fixed_oracle_run_bind,
        queryCompress_fixed, pure_bind, fixed_oracle_run_pure]
      refine ⟨Function.update f n _, rfl, ?_, ?_⟩
      · intro idx hlt
        by_cases heq : idx = n
        · subst heq
          simp only [Function.update_self, nodeValFromLeaves, show idx < FULL_TRIPLETS by omega, ite_true]
          have h0 := hl0_all (3 * idx) (by rw [levelSize_0, full_triplets_eq] at *; omega)
          have h1 := hl0_all (3 * idx + 1) (by rw [levelSize_0, full_triplets_eq] at *; omega)
          have h2 := hl0_all (3 * idx + 2) (by rw [levelSize_0, full_triplets_eq] at *; omega)
          rw [h0, h1, h2]
          rfl
        · rw [Function.update_of_ne heq]; exact hval idx (by omega)
      · rw [Function.update_of_ne (by omega)]; exact hprom
  obtain ⟨l1, hl1_run, hl1_lt, hl1_prom⟩ := hl1 FULL_TRIPLETS (le_refl _)
  have hl1_all : ∀ idx < levelSize 1, l1 idx = nodeValFromLeaves c leaves 1 idx := by
    intro idx hidx
    rw [levelSize_1] at hidx
    have hft : FULL_TRIPLETS = 5592405 := full_triplets_eq
    by_cases hlt : idx < FULL_TRIPLETS
    · exact hl1_lt idx hlt
    · have heq : idx = FULL_TRIPLETS := by omega
      subst heq; exact hl1_prom
  have hbin : ∀ (prevLvl : Nat) (hge1 : 1 ≤ prevLvl) (hlt24 : prevLvl < 24)
      (prevArr : Nat → Digest) (hprev : ∀ idx < levelSize prevLvl, prevArr idx = nodeValFromLeaves c leaves prevLvl idx)
      (n : Nat) (hn : n ≤ levelSize prevLvl / 2),
      ∃ f, fixedOracleRun oracle (queryBinLevelAux h768 prevArr (levelSize prevLvl) (decide (prevLvl + 1 = 24)) n) = pure f ∧
        (∀ idx < n, f idx = nodeValFromLeaves c leaves (prevLvl + 1) idx) ∧
        (levelSize prevLvl % 2 = 1 → f (levelSize prevLvl / 2) = nodeValFromLeaves c leaves (prevLvl + 1) (levelSize prevLvl / 2)) := by
    intro prevLvl hge1 hlt24 prevArr hprev n hn
    obtain ⟨m, rfl⟩ : ∃ m, prevLvl = m + 1 := ⟨prevLvl - 1, by omega⟩
    induction n with
    | zero =>
      rw [queryBinLevelAux_zero]
      refine ⟨_, fixed_oracle_run_pure _ _, fun _ h => (Nat.not_lt_zero _ h).elim, ?_⟩
      intro hodd
      simp only [hodd, true_and, ite_true, nodeValFromLeaves]
      rw [if_neg (by omega), if_pos (by omega)]
      exact hprev (2 * (levelSize (m + 1) / 2)) (by omega)
    | succ n ih =>
      obtain ⟨f, hrun, hval, hprom⟩ := ih (by omega)
      rw [queryBinLevelAux_succ, fixed_oracle_run_bind, hrun, pure_bind, fixed_oracle_run_bind,
        queryCompress_fixed, pure_bind, fixed_oracle_run_pure]
      refine ⟨Function.update f n _, rfl, ?_, ?_⟩
      · intro idx hlt
        by_cases heq : idx = n
        · subst heq
          simp only [Function.update_self, nodeValFromLeaves, show 2 * idx + 1 < levelSize (m + 1) by omega,
            ite_true, decide_eq_true_eq]
          rw [hprev (2 * idx) (by omega), hprev (2 * idx + 1) (by omega)]
        · rw [Function.update_of_ne heq]; exact hval idx (by omega)
      · intro hodd
        rw [Function.update_of_ne (by omega)]; exact hprom hodd
  have hup : ∀ k ≤ 23, ∃ arr, fixedOracleRun oracle (queryUpperLevels h768 l0 l1 k) = pure arr ∧
      ∀ l ≤ k + 1, ∀ idx < levelSize l, arr l idx = nodeValFromLeaves c leaves l idx := by
    intro k hk; induction k with
    | zero =>
      rw [queryUpperLevels_zero]
      refine ⟨_, fixed_oracle_run_pure _ _, ?_⟩
      intro l hl idx hidx
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl with rfl | rfl
      · simp only [ite_true]; exact hl0_all idx hidx
      · simp only [show (1 : Nat) ≠ 0 by decide, ite_false, ite_true]; exact hl1_all idx hidx
    | succ k ih =>
      obtain ⟨arr, hrun, hval⟩ := ih (by omega)
      rw [queryUpperLevels_succ, fixed_oracle_run_bind, hrun, pure_bind]
      obtain ⟨cur, hcur_run, hcur_lt, hcur_prom⟩ := hbin (k + 1) (by omega) (by omega)
        (arr (k + 1)) (hval (k + 1) (by omega)) (levelSize (k + 1) / 2) (le_refl _)
      rw [fixed_oracle_run_bind, hcur_run, pure_bind, fixed_oracle_run_pure]
      refine ⟨Function.update arr (k + 2) cur, rfl, ?_⟩
      intro l hl idx hidx
      by_cases hltop : l = k + 2
      · subst hltop
        rw [Function.update_self]
        rw [levelSize_step (k + 1) (by omega)] at hidx
        by_cases hlt : idx < levelSize (k + 1) / 2
        · exact hcur_lt idx hlt
        · have hodd : levelSize (k + 1) % 2 = 1 := by omega
          have heq : idx = levelSize (k + 1) / 2 := by omega
          subst heq; exact hcur_prom hodd
      · rw [Function.update_of_ne hltop]
        exact hval l (by omega) idx hidx
  obtain ⟨nodes, hup_run, hup_val⟩ := hup 23 (le_refl _)
  rw [queryTreeFromLeafFn_def, fixed_oracle_run_bind, hl0_run, pure_bind, fixed_oracle_run_bind,
    hl1_run, pure_bind, hup_run]
  exact ⟨nodes, rfl, hup_val⟩

/-! ### 6. Pure `GoodTrace` Invariant for `queryIdeal0Tree` -/

def GoodIdeal0Query (positions : Positions) (cv0 : Index → Digest)
    (trace : CompressionReplies) (x : BitVec COMPRESSION_INPUT_LENGTH) : Prop :=
  (∃ i ∈ positions, x.extractLsb' 128 64 = leafTag i) ∨
  (∃ i ∉ positions, x.extractLsb' 0 192 = (cv0 i).extractLsb' 0 192) ∨
  (∃ pair ∈ trace, x.extractLsb' 0 192 = pair.2.extractLsb' 0 192)

def GoodIdeal0Trace (positions : Positions) (cv0 : Index → Digest) (trace : CompressionReplies) : Prop :=
  ∀ pair ∈ trace, GoodIdeal0Query positions cv0 trace pair.1

private theorem good_query_mono {positions : Positions} {cv0 : Index → Digest}
    {t1 t2 : CompressionReplies} (hsub : ∀ p ∈ t1, p ∈ t2) {x}
    (hg : GoodIdeal0Query positions cv0 t1 x) : GoodIdeal0Query positions cv0 t2 x := by
  rcases hg with h1 | h2 | ⟨p, hp, heq⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨p, hsub p hp, heq⟩)

private theorem traceReplies_pure {α : Type} (v : α) :
    traceCompressionReplies (pure v : OracleComp World α) = pure (v, []) := rfl

private theorem traceReplies_bind {α β : Type} (comp : OracleComp World α)
    (next : α → OracleComp World β) :
    traceCompressionReplies (comp >>= next) = (do
      let p1 ← traceCompressionReplies comp
      let p2 ← traceCompressionReplies (next p1.1)
      pure (p2.1, p1.2 ++ p2.2)) := by
  induction comp using OracleComp.inductionOn with
  | pure v => simp [traceReplies_pure]
  | query_bind q k ih =>
    rcases q with coins | pq
    · change ((liftM (World.query (.inl coins)) : OracleComp World _) >>= fun ans =>
          traceCompressionReplies (k ans >>= next)) =
        (((liftM (World.query (.inl coins)) : OracleComp World _) >>= fun ans =>
          traceCompressionReplies (k ans)) >>= fun p1 =>
            traceCompressionReplies (next p1.1) >>= fun p2 => pure (p2.1, p1.2 ++ p2.2))
      rw [bind_assoc]
      exact bind_congr ih
    · rcases pq with inp | permq
      · change ((liftM (World.query (.inr (.inl inp))) : OracleComp World Digest) >>= fun (ans : Digest) =>
            traceCompressionReplies (k ans >>= next) >>= fun (v, tr) => pure (v, (inp, ans) :: tr)) =
          (((liftM (World.query (.inr (.inl inp))) : OracleComp World Digest) >>= fun (ans : Digest) =>
            traceCompressionReplies (k ans) >>= fun (v, tr) => pure (v, (inp, ans) :: tr)) >>=
              fun p1 => traceCompressionReplies (next p1.1) >>= fun p2 => pure (p2.1, p1.2 ++ p2.2))
        rw [bind_assoc]
        apply bind_congr; intro ans
        rw [ih ans, bind_assoc, bind_assoc]
        apply bind_congr; rintro ⟨a, t1⟩
        simp only [pure_bind, bind_assoc]
        apply bind_congr; rintro ⟨b, t2⟩
        simp only [pure_bind, List.cons_append]
      · change ((liftM (World.query (.inr (.inr permq))) : OracleComp World _) >>= fun ans =>
            traceCompressionReplies (k ans >>= next)) =
          (((liftM (World.query (.inr (.inr permq))) : OracleComp World _) >>= fun ans =>
            traceCompressionReplies (k ans)) >>= fun p1 =>
              traceCompressionReplies (next p1.1) >>= fun p2 => pure (p2.1, p1.2 ++ p2.2))
        rw [bind_assoc]
        exact bind_congr ih

private theorem traceReplies_queryCompress_fixed (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (x : BitVec 768) :
    fixedOracleRun oracle (traceCompressionReplies (queryCompress h768 x)) =
      (pure (oracle.compression (x.cast h768.symm),
        [(x.cast h768.symm, (oracle.compression (x.cast h768.symm) : Digest))]) :
        ProbComp (Digest × CompressionReplies)) := by
  unfold queryCompress
  change fixedOracleRun oracle ((liftM (World.query (.inr (.inl (x.cast h768.symm)))) : OracleComp World Digest) >>=
    fun (ans : Digest) => (pure (ans, ([] : CompressionReplies)) : OracleComp World (Digest × CompressionReplies)) >>=
      fun (v, tr) => pure (v, (x.cast h768.symm, ans) :: tr)) = _
  rw [fixed_oracle_run_compress, pure_bind]
  exact fixed_oracle_run_pure oracle (α := Digest × CompressionReplies) _

def ideal0LeafFn (h768 : COMPRESSION_INPUT_LENGTH = 768) (msg : Message)
    (sOpen : Index → Salt128) (cv0 : Index → Digest) (positions : Positions) (i : Index) :
    OracleComp World Digest :=
  if i ∈ positions then queryLeafOpened h768 i (sOpen i) (msg i)
  else queryLeafFromCv0 h768 (cv0 i) (msg i)

/-- Every single compression query executed during `queryTreeFromLeafFn (ideal0LeafFn ...)`
satisfies `GoodIdeal0Trace`: its low 192 bits either carry an opened leaf tag, a `cv0 i` prefix,
or an earlier compression output from the same trace. -/
theorem queryIdeal0Tree_good_trace (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (sOpen : Index → Salt128) (cv0 : Index → Digest)
    (positions : Positions) :
    ∃ nodes trace,
      fixedOracleRun oracle (traceCompressionReplies
        (queryTreeFromLeafFn h768 (ideal0LeafFn h768 msg sOpen cv0 positions))) = pure (nodes, trace) ∧
      GoodIdeal0Trace positions cv0 trace := by
  have hcast192 : ∀ (x : BitVec 768), (x.cast h768.symm).extractLsb' 0 192 = x.extractLsb' 0 192 :=
    fun x => extractLsb'_cast_eq h768.symm x 0 192
  have hcastTag : ∀ (x : BitVec 768), (x.cast h768.symm).extractLsb' 128 64 = x.extractLsb' 128 64 :=
    fun x => extractLsb'_cast_eq h768.symm x 128 64
  have hleaf : ∀ i : Index, ∃ d tr,
      fixedOracleRun oracle (traceCompressionReplies (ideal0LeafFn h768 msg sOpen cv0 positions i)) = pure (d, tr) ∧
      GoodIdeal0Trace positions cv0 tr ∧
      ∃ p ∈ tr, d.extractLsb' 0 192 = p.2.extractLsb' 0 192 := by
    intro i
    unfold ideal0LeafFn
    by_cases hi : i ∈ positions
    · rw [if_pos hi]
      unfold queryLeafOpened
      let x0 := (leafCall0Input i (sOpen i) (msg i)).cast h768.symm
      let d0 : Digest := oracle.compression x0
      let x1 := (leafCall1Input d0 (msg i)).cast h768.symm
      let d1 : Digest := oracle.compression x1
      let x2 := (leafCall2Input d1 (msg i)).cast h768.symm
      let d2 : Digest := oracle.compression x2
      let x3 := (leafCall3Input d2 (msg i)).cast h768.symm
      let d3 : Digest := oracle.compression x3
      have hrun_leaf :
          fixedOracleRun oracle (traceCompressionReplies (do
            let cv0 ← queryCompress h768 (leafCall0Input i (sOpen i) (msg i))
            let cv1 ← queryCompress h768 (leafCall1Input cv0 (msg i))
            let cv2 ← queryCompress h768 (leafCall2Input cv1 (msg i))
            queryCompress h768 (leafCall3Input cv2 (msg i)))) =
          pure (d3, [(x0, d0), (x1, d1), (x2, d2), (x3, d3)]) := by
        simp only [traceReplies_bind, fixed_oracle_run_bind, traceReplies_queryCompress_fixed, pure_bind,
          fixed_oracle_run_pure, List.cons_append, List.nil_append]
        rfl
      refine ⟨d3, [(x0, d0), (x1, d1), (x2, d2), (x3, d3)], hrun_leaf, ?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl
        · left; refine ⟨i, hi, ?_⟩
          dsimp only [x0]; rw [hcastTag, leafCall0Input_tag]
        · right; right; refine ⟨(x0, d0), by simp, ?_⟩
          dsimp only [x1]; rw [hcast192]; unfold leafCall1Input
          exact extractLsb'_0_192_append_digest _ _
        · right; right; refine ⟨(x1, d1), by simp, ?_⟩
          dsimp only [x2]; rw [hcast192]; unfold leafCall2Input
          exact extractLsb'_0_192_append_digest _ _
        · right; right; refine ⟨(x2, d2), by simp, ?_⟩
          dsimp only [x3]; rw [hcast192]; unfold leafCall3Input
          exact extractLsb'_0_192_append_digest _ _
      · exact ⟨(x3, d3), by simp, rfl⟩
    · rw [if_neg hi]
      unfold queryLeafFromCv0
      let x1 := (leafCall1Input (cv0 i) (msg i)).cast h768.symm
      let d1 : Digest := oracle.compression x1
      let x2 := (leafCall2Input d1 (msg i)).cast h768.symm
      let d2 : Digest := oracle.compression x2
      let x3 := (leafCall3Input d2 (msg i)).cast h768.symm
      let d3 : Digest := oracle.compression x3
      have hrun_leaf :
          fixedOracleRun oracle (traceCompressionReplies (do
            let cv1 ← queryCompress h768 (leafCall1Input (cv0 i) (msg i))
            let cv2 ← queryCompress h768 (leafCall2Input cv1 (msg i))
            queryCompress h768 (leafCall3Input cv2 (msg i)))) =
          pure (d3, [(x1, d1), (x2, d2), (x3, d3)]) := by
        simp only [traceReplies_bind, fixed_oracle_run_bind, traceReplies_queryCompress_fixed, pure_bind,
          fixed_oracle_run_pure, List.cons_append, List.nil_append]
        rfl
      refine ⟨d3, [(x1, d1), (x2, d2), (x3, d3)], hrun_leaf, ?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl
        · right; left; refine ⟨i, hi, ?_⟩
          dsimp only [x1]; rw [hcast192]; unfold leafCall1Input
          exact extractLsb'_0_192_append_digest _ _
        · right; right; refine ⟨(x1, d1), by simp, ?_⟩
          dsimp only [x2]; rw [hcast192]; unfold leafCall2Input
          exact extractLsb'_0_192_append_digest _ _
        · right; right; refine ⟨(x2, d2), by simp, ?_⟩
          dsimp only [x3]; rw [hcast192]; unfold leafCall3Input
          exact extractLsb'_0_192_append_digest _ _
      · exact ⟨(x3, d3), by simp, rfl⟩
  have hl0 : ∀ n, ∃ f tr,
      fixedOracleRun oracle (traceCompressionReplies (queryLevel0Aux (ideal0LeafFn h768 msg sOpen cv0 positions) n)) = pure (f, tr) ∧
      GoodIdeal0Trace positions cv0 tr ∧
      ∀ idx < n, idx < LENGTH → ∃ p ∈ tr, (f idx).extractLsb' 0 192 = p.2.extractLsb' 0 192 := by
    intro n; induction n with
    | zero =>
      exact ⟨fun _ => 0, [], by simp only [queryLevel0Aux_zero, traceReplies_pure, fixed_oracle_run_pure],
        by simp [GoodIdeal0Trace], fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ n ih =>
      obtain ⟨f, tr, hrun, hgood, hnodes⟩ := ih
      rw [queryLevel0Aux_succ, traceReplies_bind, fixed_oracle_run_bind, hrun, pure_bind]
      dsimp only
      by_cases hn : n < LENGTH
      · rw [dif_pos hn]
        obtain ⟨d, trd, hdrun, hdgood, hdp⟩ := hleaf ⟨n, hn⟩
        simp only [traceReplies_bind, traceReplies_pure, fixed_oracle_run_bind, fixed_oracle_run_pure,
          hdrun, pure_bind, List.append_nil]
        refine ⟨Function.update f n d, tr ++ trd, rfl, ?_, ?_⟩
        · intro p hp
          rcases List.mem_append.mp hp with hp1 | hp2
          · exact good_query_mono (fun q hq => List.mem_append_left _ hq) (hgood p hp1)
          · exact good_query_mono (fun q hq => List.mem_append_right _ hq) (hdgood p hp2)
        · intro idx hlt hlen
          by_cases heq : idx = n
          · subst heq; rw [Function.update_self]
            obtain ⟨p, hp, hpeq⟩ := hdp
            exact ⟨p, List.mem_append_right _ hp, hpeq⟩
          · rw [Function.update_of_ne heq]
            obtain ⟨p, hp, hpeq⟩ := hnodes idx (by omega) hlen
            exact ⟨p, List.mem_append_left _ hp, hpeq⟩
      · rw [dif_neg hn]
        simp only [traceReplies_pure, fixed_oracle_run_pure, pure_bind, List.append_nil]
        exact ⟨f, tr, rfl, hgood, fun idx hlt hlen => hnodes idx (by omega) hlen⟩
  obtain ⟨l0, tr0, htr0_run, htr0_good, htr0_nodes⟩ := hl0 LENGTH
  have hl1 : ∀ n, n ≤ FULL_TRIPLETS → ∃ f tr,
      fixedOracleRun oracle (traceCompressionReplies (queryLevel1Aux h768 l0 n)) = pure (f, tr) ∧
      GoodIdeal0Trace positions cv0 (tr0 ++ tr) ∧
      (∀ idx < n, ∃ p ∈ tr0 ++ tr, (f idx).extractLsb' 0 192 = p.2.extractLsb' 0 192) ∧
      (∃ p ∈ tr0 ++ tr, (f FULL_TRIPLETS).extractLsb' 0 192 = p.2.extractLsb' 0 192) := by
    intro n hn; induction n with
    | zero =>
      refine ⟨fun idx => if idx = FULL_TRIPLETS then l0 (3 * FULL_TRIPLETS) else 0, [],
        by simp only [queryLevel1Aux_zero, traceReplies_pure, fixed_oracle_run_pure], by simpa using htr0_good,
        fun _ h => (Nat.not_lt_zero _ h).elim, ?_⟩
      simp only [List.append_nil, ite_true]
      exact htr0_nodes (3 * FULL_TRIPLETS) (by rw [full_triplets_eq]; unfold LENGTH LOG_LENGTH; omega)
        (by rw [full_triplets_eq]; unfold LENGTH LOG_LENGTH; omega)
    | succ n ih =>
      obtain ⟨f, tr, hrun, hgood, hval, hprom⟩ := ih (by omega)
      rw [queryLevel1Aux_succ]
      let x := (ternaryInput (l0 (3 * n)) (l0 (3 * n + 1)) (l0 (3 * n + 2))).cast h768.symm
      let d : Digest := oracle.compression x
      have hrun1 :
          fixedOracleRun oracle (traceCompressionReplies (do
            let prev ← queryLevel1Aux h768 l0 n
            let d' ← queryCompress h768 (ternaryInput (l0 (3 * n)) (l0 (3 * n + 1)) (l0 (3 * n + 2)))
            pure (Function.update prev n d'))) =
          pure (Function.update f n d, tr ++ [(x, d)]) := by
        simp only [traceReplies_bind, traceReplies_pure, fixed_oracle_run_bind, fixed_oracle_run_pure,
          traceReplies_queryCompress_fixed, hrun, pure_bind, List.append_nil]
        rfl
      refine ⟨Function.update f n d, tr ++ [(x, d)], hrun1, ?_, ?_, ?_⟩
      · intro p hp
        have hmem_sub : ∀ q ∈ tr0 ++ tr, q ∈ tr0 ++ (tr ++ [(x, d)]) := by
          intro q hq
          rcases List.mem_append.mp hq with h1 | h2
          · exact List.mem_append_left _ h1
          · exact List.mem_append_right _ (List.mem_append_left _ h2)
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with h1 | (h2 | rfl)
        · exact good_query_mono hmem_sub (hgood p (List.mem_append_left _ h1))
        · exact good_query_mono hmem_sub (hgood p (List.mem_append_right _ h2))
        · right; right
          obtain ⟨q, hq, hqeq⟩ := htr0_nodes (3 * n) (by rw [full_triplets_eq] at *; unfold LENGTH LOG_LENGTH; omega)
            (by rw [full_triplets_eq] at *; unfold LENGTH LOG_LENGTH; omega)
          refine ⟨q, List.mem_append_left _ hq, ?_⟩
          dsimp only [x]; rw [hcast192, ← hqeq]
          unfold ternaryInput
          exact extractLsb'_0_192_append_digest _ _
      · intro idx hlt
        by_cases heq : idx = n
        · subst heq; rw [Function.update_self]
          exact ⟨(x, d), by simp, rfl⟩
        · rw [Function.update_of_ne heq]
          obtain ⟨p, hp, hpeq⟩ := hval idx (by omega)
          refine ⟨p, ?_, hpeq⟩
          rcases List.mem_append.mp hp with h1 | h2
          · exact List.mem_append_left _ h1
          · exact List.mem_append_right _ (List.mem_append_left _ h2)
      · rw [Function.update_of_ne (by omega)]
        obtain ⟨p, hp, hpeq⟩ := hprom
        refine ⟨p, ?_, hpeq⟩
        rcases List.mem_append.mp hp with h1 | h2
        · exact List.mem_append_left _ h1
        · exact List.mem_append_right _ (List.mem_append_left _ h2)
  obtain ⟨l1, tr1, htr1_run, htr1_good, htr1_lt, htr1_prom⟩ := hl1 FULL_TRIPLETS (le_refl _)
  have hbin : ∀ (prevTr : CompressionReplies) (hpg : GoodIdeal0Trace positions cv0 prevTr)
      (prevArr : Nat → Digest) (ps : Nat) (ir : Bool)
      (hprev : ∀ idx < ps, ∃ p ∈ prevTr, (prevArr idx).extractLsb' 0 192 = p.2.extractLsb' 0 192)
      (n : Nat) (hn : n ≤ ps / 2),
      ∃ f tr,
        fixedOracleRun oracle (traceCompressionReplies (queryBinLevelAux h768 prevArr ps ir n)) = pure (f, tr) ∧
        GoodIdeal0Trace positions cv0 (prevTr ++ tr) ∧
        (∀ idx < n, ∃ p ∈ prevTr ++ tr, (f idx).extractLsb' 0 192 = p.2.extractLsb' 0 192) ∧
        (ps % 2 = 1 → ∃ p ∈ prevTr ++ tr, (f (ps / 2)).extractLsb' 0 192 = p.2.extractLsb' 0 192) := by
    intro prevTr hpg prevArr ps ir hprev n hn
    induction n with
    | zero =>
      refine ⟨fun idx => if ps % 2 = 1 ∧ idx = ps / 2 then prevArr (2 * idx) else 0, [],
        by simp only [queryBinLevelAux_zero, traceReplies_pure, fixed_oracle_run_pure], by simpa using hpg,
        fun _ h => (Nat.not_lt_zero _ h).elim, ?_⟩
      intro hodd
      simp only [List.append_nil, hodd, true_and, ite_true]
      exact hprev (2 * (ps / 2)) (by omega)
    | succ n ih =>
      obtain ⟨f, tr, hrun, hgood, hval, hprom⟩ := ih (by omega)
      rw [queryBinLevelAux_succ]
      let x := (binaryInput (prevArr (2 * n)) (prevArr (2 * n + 1))).cast h768.symm
      let raw : Digest := oracle.compression x
      let d : Digest := if ir then raw else mask240 raw
      have hrunb :
          fixedOracleRun oracle (traceCompressionReplies (do
            let prev ← queryBinLevelAux h768 prevArr ps ir n
            let raw' ← queryCompress h768 (binaryInput (prevArr (2 * n)) (prevArr (2 * n + 1)))
            let d' := if ir then raw' else mask240 raw'
            pure (Function.update prev n d'))) =
          pure (Function.update f n d, tr ++ [(x, raw)]) := by
        simp only [traceReplies_bind, traceReplies_pure, fixed_oracle_run_bind, fixed_oracle_run_pure,
          traceReplies_queryCompress_fixed, hrun, pure_bind, List.append_nil]
        rfl
      refine ⟨Function.update f n d, tr ++ [(x, raw)], hrunb, ?_, ?_, ?_⟩
      · intro p hp
        have hmem_sub : ∀ q ∈ prevTr ++ tr, q ∈ prevTr ++ (tr ++ [(x, raw)]) := by
          intro q hq
          rcases List.mem_append.mp hq with h1 | h2
          · exact List.mem_append_left _ h1
          · exact List.mem_append_right _ (List.mem_append_left _ h2)
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with h1 | (h2 | rfl)
        · exact good_query_mono hmem_sub (hgood p (List.mem_append_left _ h1))
        · exact good_query_mono hmem_sub (hgood p (List.mem_append_right _ h2))
        · right; right
          obtain ⟨q, hq, hqeq⟩ := hprev (2 * n) (by omega)
          refine ⟨q, List.mem_append_left _ hq, ?_⟩
          dsimp only [x]; rw [hcast192, ← hqeq]
          unfold binaryInput
          exact extractLsb'_0_192_append_digest _ _
      · intro idx hlt
        by_cases heq : idx = n
        · subst heq; rw [Function.update_self]
          refine ⟨(x, raw), by simp, ?_⟩
          dsimp only [d]
          cases ir
          · exact extractLsb'_192_mask240 raw
          · rfl
        · rw [Function.update_of_ne heq]
          obtain ⟨p, hp, hpeq⟩ := hval idx (by omega)
          refine ⟨p, ?_, hpeq⟩
          rcases List.mem_append.mp hp with h1 | h2
          · exact List.mem_append_left _ h1
          · exact List.mem_append_right _ (List.mem_append_left _ h2)
      · intro hodd
        rw [Function.update_of_ne (by omega)]
        obtain ⟨p, hp, hpeq⟩ := hprom hodd
        refine ⟨p, ?_, hpeq⟩
        rcases List.mem_append.mp hp with h1 | h2
        · exact List.mem_append_left _ h1
        · exact List.mem_append_right _ (List.mem_append_left _ h2)
  have hup : ∀ k ≤ 23, ∃ arr tr,
      fixedOracleRun oracle (traceCompressionReplies (queryUpperLevels h768 l0 l1 k)) = pure (arr, tr) ∧
      GoodIdeal0Trace positions cv0 ((tr0 ++ tr1) ++ tr) ∧
      ∀ l ≤ k + 1, ∀ idx < levelSize l, ∃ p ∈ (tr0 ++ tr1) ++ tr, (arr l idx).extractLsb' 0 192 = p.2.extractLsb' 0 192 := by
    intro k hk; induction k with
    | zero =>
      refine ⟨fun l idx => if l = 0 then l0 idx else if l = 1 then l1 idx else 0, [],
        by simp only [queryUpperLevels_zero, traceReplies_pure, fixed_oracle_run_pure], by simpa using htr1_good, ?_⟩
      intro l hl idx hidx
      simp only [List.append_nil]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl with rfl | rfl
      · simp only [ite_true]
        have hidx' : idx < LENGTH := by rwa [levelSize_0, show (16777216 : Nat) = LENGTH by decide] at hidx
        obtain ⟨p, hp, hpeq⟩ := htr0_nodes idx hidx' hidx'
        exact ⟨p, List.mem_append_left _ hp, hpeq⟩
      · simp only [show (1 : Nat) ≠ 0 by decide, ite_false, ite_true]
        rw [levelSize_1] at hidx
        have hft := full_triplets_eq
        by_cases hlt : idx < FULL_TRIPLETS
        · exact htr1_lt idx hlt
        · have heq : idx = FULL_TRIPLETS := by omega
          subst heq; exact htr1_prom
    | succ k ih =>
      obtain ⟨arr, tr, hrun, hgood, hval⟩ := ih (by omega)
      rw [queryUpperLevels_succ, traceReplies_bind, fixed_oracle_run_bind, hrun, pure_bind]
      dsimp only
      obtain ⟨cur, trc, hcrun, hcgood, hclt, hcprom⟩ := hbin ((tr0 ++ tr1) ++ tr) hgood
        (arr (k + 1)) (levelSize (k + 1)) (decide (k + 2 = 24)) (hval (k + 1) (by omega))
        (levelSize (k + 1) / 2) (le_refl _)
      simp only [traceReplies_bind, traceReplies_pure, fixed_oracle_run_bind, fixed_oracle_run_pure,
        hcrun, pure_bind, List.append_nil]
      refine ⟨Function.update arr (k + 2) cur, tr ++ trc, rfl, ?_, ?_⟩
      · simpa [List.append_assoc] using hcgood
      · intro l hl idx hidx
        by_cases htop : l = k + 2
        · subst htop; rw [Function.update_self]
          rw [levelSize_step (k + 1) (by omega)] at hidx
          by_cases hlt : idx < levelSize (k + 1) / 2
          · simpa [List.append_assoc] using hclt idx hlt
          · have hodd : levelSize (k + 1) % 2 = 1 := by omega
            have heq : idx = levelSize (k + 1) / 2 := by omega
            subst heq; simpa [List.append_assoc] using hcprom hodd
        · rw [Function.update_of_ne htop]
          obtain ⟨p, hp, hpeq⟩ := hval l (by omega) idx hidx
          refine ⟨p, ?_, hpeq⟩
          rcases List.mem_append.mp hp with h1 | h2
          · exact List.mem_append_left _ h1
          · exact List.mem_append_right _ (List.mem_append_left _ h2)
  obtain ⟨nodes, trUp, hup_run, hup_good, _⟩ := hup 23 (le_refl _)
  rw [queryTreeFromLeafFn_def]
  simp only [traceReplies_bind, fixed_oracle_run_bind, fixed_oracle_run_pure,
    htr0_run, htr1_run, hup_run, pure_bind]
  exact ⟨nodes, tr0 ++ (tr1 ++ trUp), rfl, by simpa [List.append_assoc] using hup_good⟩

end CommitGolfCandidate
