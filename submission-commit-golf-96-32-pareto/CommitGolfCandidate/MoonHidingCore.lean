import CommitGolfCandidate.MoonBinding
import CommitGolfCandidate.HidingTrace
import Mathlib.Data.Fintype.EquivFin

/-! Core probabilistic, lazy-ROM, identical-until-bad, and pure-binary tree-query primitives
for the B1-Ultra-121 (`121`-bit early-tagged independent salt) statistical hiding proof:
- `splitSalts121` & `saltsMerge` bijective uniform sampling identities
- Combined Stage-1/Stage-2 query budget tracking (`first_stage_combined_budget`: `q1 + q2 <= budget`)
- One-sided identical-until-bad TV inequality (`measureTVDist_one_sided_with_slack`)
- `flagComp` pure `OracleComp` query-flagging wrapper matching `flaggedRun`
- 256-bit chaining-value hiding (`cached_chain3_distance`) for leaf Calls 1..3
- Pure-binary `r = 0` bottom-up tree evaluation (`HONEST_TREE_BUDGET = 4*2^24 + 2^24 - 1`) and
  its `GoodIdeal0Trace` invariant under uniform `238`-bit masking (`L0..L23`). -/
namespace CommitGolfCandidate

local instance moonHidingCoreDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
local instance moonHidingCoreDiscrete {α : Type} : DiscreteMeasurableSpace α := ⟨fun _ => trivial⟩
local instance moonHidingCoreProdBoolDiscrete {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] :
    DiscreteMeasurableSpace (α × Bool) :=
  ⟨fun s => by
    have h : s = ({a | (a, false) ∈ s} ×ˢ ({false} : Set Bool)) ∪
                 ({a | (a, true) ∈ s} ×ˢ ({true} : Set Bool)) := by
      ext ⟨a, b⟩; cases b <;> simp
    rw [h]
    exact (MeasurableSet.prod MeasurableSet.of_discrete MeasurableSet.of_discrete).union
      (MeasurableSet.prod MeasurableSet.of_discrete MeasurableSet.of_discrete)⟩

local instance moonHidingCoreProdUnitBoolDiscrete {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] :
    DiscreteMeasurableSpace (α × Unit × Bool) :=
  ⟨fun s => by
    have h : s = ({a | (a, (), false) ∈ s} ×ˢ ({((), false)} : Set (Unit × Bool))) ∪
                 ({a | (a, (), true) ∈ s} ×ˢ ({((), true)} : Set (Unit × Bool))) := by
      ext ⟨a, ⟨⟨⟩, b⟩⟩; cases b <;> simp
    rw [h]
    exact (MeasurableSet.prod MeasurableSet.of_discrete MeasurableSet.of_discrete).union
      (MeasurableSet.prod MeasurableSet.of_discrete MeasurableSet.of_discrete)⟩
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling OracleComp.ProgramLogic.Relational
open MeasureTheory
open scoped ENNReal

/-! ### 1. Bulk 16-Byte RANDOM Splitting, 121-Bit Truncation, and Opened/Hidden Salt Split -/

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

def splitSalts121 (packed : BitVec (128 * LENGTH)) : Index → Salt121 :=
  fun i => (splitBlocks 128 LENGTH packed i).extractLsb' 0 121

theorem prod_uniform_bind {A B α : Type} [SampleableType A] [SampleableType B]
    (next : A × B → ProbComp α) :
    𝒟[do let a ← $ᵗ A
         let b ← $ᵗ B
         next (a, b)] =
      𝒟[($ᵗ (A × B)) >>= next] := by
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]

private def split128To121x7 (raw : Index → BitVec 128) :
    (Index → Salt121) × (Index → BitVec 7) :=
  (fun i => (raw i).extractLsb' 0 121, fun i => (raw i).extractLsb' 121 7)

private theorem split128To121x7_bijective : Function.Bijective split128To121x7 := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun p i => p.2 i ++ p.1 i, ?_, ?_⟩
  · intro raw
    funext i
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    unfold split128To121x7
    rw [BitVec.getLsbD_append]
    by_cases h121 : b < 121
    · simp [h121]
    · have h7 : b - 121 < 7 := by omega
      simp [h121, h7, show 121 + (b - 121) = b by omega]
  · rintro ⟨lo, hi⟩
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · exact BitVec.extractLsb'_append_eq_right
    · dsimp only [split128To121x7]
      rw [BitVec.extractLsb'_append_eq_of_le (by decide : 121 ≤ 121)]
      simp

theorem splitSalts121_uniform_bind {α : Type} (next : (Index → Salt121) → ProbComp α) :
    𝒟[($ᵗ BitVec (128 * LENGTH)) >>= fun packed => next (splitSalts121 packed)] =
      𝒟[($ᵗ (Index → Salt121)) >>= next] := by
  have h1 := split_blocks_uniform_bind 128 LENGTH (by decide)
    (fun raw => next (fun i => (raw i).extractLsb' 0 121))
  change 𝒟[($ᵗ BitVec (128 * LENGTH)) >>= fun packed => next (fun i => (splitBlocks 128 LENGTH packed i).extractLsb' 0 121)] = _
  rw [h1]
  have h2 : 𝒟[($ᵗ (Index → BitVec 128)) >>= fun raw => next (split128To121x7 raw).1] =
      𝒟[($ᵗ ((Index → Salt121) × (Index → BitVec 7))) >>= fun p => next p.1] := by
    have hmap := ((SampleableType.map_uniformSample_evalDistEq_of_bijective split128To121x7_bijective).bind_left
      (fun p : (Index → Salt121) × (Index → BitVec 7) => next p.1)).evalDist_eq
    rw [bind_map_left] at hmap
    exact hmap
  change 𝒟[($ᵗ (Index → BitVec 128)) >>= fun raw => next (split128To121x7 raw).1] = _
  rw [h2, ← prod_uniform_bind (fun p : (Index → Salt121) × (Index → BitVec 7) => next p.1)]
  apply _root_.evalDist_bind_congr
  intro lo
  exact OracleComp.evalDist_bind_const ($ᵗ (Index → BitVec 7)) (next lo)

def saltsMerge (positions : Positions) (sOpen sHidden : Index → Salt121) : Index → Salt121 :=
  fun i => if i ∈ positions then sOpen i else sHidden i

theorem saltsMerge_uniform_bind (positions : Positions) {α : Type}
    (next : (Index → Salt121) → ProbComp α) :
    𝒟[do let sOpen ← $ᵗ (Index → Salt121)
         let sHidden ← $ᵗ (Index → Salt121)
         next (saltsMerge positions sOpen sHidden)] =
      𝒟[($ᵗ (Index → Salt121)) >>= next] := by
  let sw : (Index → Salt121) × (Index → Salt121) → (Index → Salt121) × (Index → Salt121) :=
    fun p => (saltsMerge positions p.1 p.2, fun i => if i ∈ positions then p.2 i else p.1 i)
  have hsw_inv : ∀ p, sw (sw p) = p := by
    rintro ⟨a, b⟩
    refine Prod.ext ?_ ?_ <;> (funext i; by_cases hi : i ∈ positions <;> simp [sw, saltsMerge, hi])
  have hsw_bij : Function.Bijective sw :=
    Function.bijective_iff_has_inverse.mpr ⟨sw, hsw_inv, hsw_inv⟩
  rw [prod_uniform_bind (fun p : (Index → Salt121) × (Index → Salt121) => next (sw p).1)]
  have hmap := ((SampleableType.map_uniformSample_evalDistEq_of_bijective hsw_bij).bind_left
    (fun p : (Index → Salt121) × (Index → Salt121) => next p.1)).evalDist_eq
  rw [bind_map_left] at hmap
  rw [hmap, ← prod_uniform_bind (fun p : (Index → Salt121) × (Index → Salt121) => next p.1)]
  apply _root_.evalDist_bind_congr
  intro s1
  exact OracleComp.evalDist_bind_const ($ᵗ (Index → Salt121)) (next s1)

theorem evalDistEq_bind_comm {α β γ : Type} [Countable α]
    (mx : ProbComp α) (my : ProbComp β) (f : α → β → ProbComp γ) :
    (do let a ← mx; let b ← my; f a b) =ᵈ (do let b ← my; let a ← mx; f a b) :=
  EvalDistEq.of_evalDist_eq (distribution_bind_comm mx my f)

theorem evalDist_bind_comm_any {α β γ : Type} [Countable α] [MeasurableSpace γ]
    (mx : ProbComp α) (my : ProbComp β) (f : α → β → ProbComp γ) :
    𝒟[do let a ← mx; let b ← my; f a b] = 𝒟[do let b ← my; let a ← mx; f a b] :=
  (evalDistEq_bind_comm mx my f).evalDist_eq

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

theorem uniform_coordinate_bind_eq {D R α : Type} [DecidableEq D] [Finite D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)]
    (index : D) (next : (D → R) → ProbComp α) :
    (do let values ← $ᵗ (D → R)
        let value ← $ᵗ R
        next (Function.update values index value)) =ᵈ
    (do let values ← $ᵗ (D → R); next values) :=
  EvalDistEq.of_evalDist_eq (uniform_coordinate_bind index next)

theorem uniform_coordinate_bind_any {D R α : Type} [MeasurableSpace α]
    [DecidableEq D] [Finite D] [Finite R] [Nonempty R] [SampleableType R] [SampleableType (D → R)]
    (index : D) (next : (D → R) → ProbComp α) :
    𝒟[do let values ← $ᵗ (D → R)
         let value ← $ᵗ R
         next (Function.update values index value)] =
    𝒟[do let values ← $ᵗ (D → R); next values] :=
  (uniform_coordinate_bind_eq index next).evalDist_eq

/-! ### 2. Stage-1 Lazy Sampling & Exact Combined Budget Split (`q1 + q2 <= budget`) -/

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

private theorem counted_query_support' {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) (answer : World.Range query)
    (result : α × Nat) (reached : result ∈ support (Hiding.counted (next answer))) :
    (result.1, Oracle.callCost query + result.2) ∈ support
      (Hiding.counted ((liftM (World.query query) : OracleComp World _) >>= next)) := by
  rw [Hiding.counted, costDist, instrumentedRun, simulateQ_bind, simulateQ_query, WriterT.run_bind]
  refine (mem_support_bind_iff _ _ _).mpr
    ⟨(answer, (Multiplicative.ofAdd (Oracle.callCost query) : Multiplicative Nat)), ?_, ?_⟩
  · simp [QueryImpl.withAddCost, QueryImpl.withCost]
  · change (result.1, Oracle.callCost query + result.2) ∈ support
      ((fun value : α × Nat => (value.1, Oracle.callCost query + value.2)) <$>
        Hiding.counted (next answer))
    rw [support_map]
    exact ⟨result, reached, by simp [Nat.add_comm]⟩

/-- Track the EXACT syntactic call count `calls` alongside cache coverage during Stage 1,
preserving `keys.card ≤ known.card + calls` AND `(result.1, calls) ∈ support (Hiding.counted comp)`. -/
theorem compression_run_counted_covered (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (cache : CompressionCache)
    (known : Finset CompressionSpec.Domain) (covered : ∀ key, cache key ≠ none → key ∈ known)
    (result : α × CompressionCache)
    (reached : result ∈ support (compressionRun permutation computation cache)) :
    ∃ (calls : Nat) (keys : Finset CompressionSpec.Domain),
      (result.1, calls) ∈ support (Hiding.counted computation) ∧
      keys.card ≤ known.card + calls ∧
      ∀ key, result.2 key ≠ none → key ∈ keys := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache known result with
  | pure value =>
    rw [compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    refine ⟨0, known, ?_, by omega, covered⟩
    change (value, 0) ∈ support (pure (value, 0))
    simp
  | query_bind query next ih =>
    rcases query with coins | publicQuery
    · rw [compression_run_private] at reached
      obtain ⟨answer, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
      obtain ⟨calls, keys, hcnt, hcard, hcov⟩ := ih answer cache known covered result reached
      refine ⟨calls, keys, ?_, hcard, hcov⟩
      simpa [Oracle.callCost] using counted_query_support' (.inl coins) next answer (result.1, calls) hcnt
    · rcases publicQuery with input | permQuery
      · rw [compression_run_compress] at reached
        cases cached : cache input with
        | some answer =>
          rw [cached] at reached
          obtain ⟨calls, keys, hcnt, hcard, hcov⟩ := ih answer cache known covered result reached
          refine ⟨calls + 1, keys, ?_, by omega, hcov⟩
          simpa [Oracle.callCost, Nat.add_comm] using
            counted_query_support' (.inr (.inl input)) next answer (result.1, calls) hcnt
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
          obtain ⟨calls, keys, hcnt, hcard, hcov⟩ :=
            ih answer (cache.cacheQuery input answer) (insert input known) nextCovered result reached
          have hcard_ins := Finset.card_insert_le input known
          refine ⟨calls + 1, keys, ?_, by omega, hcov⟩
          simpa [Oracle.callCost, Nat.add_comm] using
            counted_query_support' (.inr (.inl input)) next answer (result.1, calls) hcnt
      · rcases permQuery with input | input
        · rw [compression_run_permute] at reached
          obtain ⟨calls, keys, hcnt, hcard, hcov⟩ := ih _ cache known covered result reached
          refine ⟨calls + 1, keys, ?_, by omega, hcov⟩
          simpa [Oracle.callCost, Nat.add_comm] using
            counted_query_support' (.inr (.inr (.inl input))) next _ (result.1, calls) hcnt
        · rw [compression_run_inverse] at reached
          obtain ⟨calls, keys, hcnt, hcard, hcov⟩ := ih _ cache known covered result reached
          refine ⟨calls + 1, keys, ?_, by omega, hcov⟩
          simpa [Oracle.callCost, Nat.add_comm] using
            counted_query_support' (.inr (.inr (.inr input))) next _ (result.1, calls) hcnt

/-- Combined Stage-1/Stage-2 budget split: for every `(ch, cache)` reachable from Stage 1,
there exists `q1 ≤ budget` such that `cache` has at most `q1` keys AND Stage 2 (`observe`)
has budget `budget - q1`! Thus `keys.card + obsBudget ≤ budget`. -/
theorem first_stage_combined_budget {State Output : Type} {openingSize budget : Nat}
    (permutation : Perm) (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget)
    (result : Hiding.HidingChallenge State openingSize × CompressionCache)
    (reached : result ∈ support (compressionRun permutation adversary.choose ∅)) :
    ∃ (q1 : Nat) (keys : Finset CompressionSpec.Domain),
      q1 ≤ budget ∧ keys.card ≤ q1 ∧
      (∀ key, result.2 key ≠ none → key ∈ keys) ∧
      (∀ root proof, PublicQueryBound (adversary.observe result.1.aux root proof) (budget - q1)) := by
  obtain ⟨q1, keys, hcnt, hcard, hcov⟩ :=
    compression_run_counted_covered permutation adversary.choose ∅ ∅ (by simp) result reached
  have hq1_le : q1 ≤ budget := (bounded (result.1, q1) hcnt).1
  have hobs : ∀ root proof, PublicQueryBound (adversary.observe result.1.aux root proof) (budget - q1) :=
    hiding_observe_query_bound adversary bounded (result.1, q1) hcnt
  exact ⟨q1, keys, hq1_le, by simpa using hcard, hcov, hobs⟩

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

/-! ### 3. One-Sided Identical-Until-Bad, Bind Integration, and `flagComp` -/

theorem prEvent_bind_le_prEvent_add_prEvent {α β γ δ : Type}
    (m : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ) (k : α → ProbComp δ)
    (pf : β → Prop) (pg : γ → Prop) (pk : δ → Prop)
    (hstep : ∀ a, Pr{let x ← f a}[pf x] ≤ Pr{let y ← g a}[pg y] + Pr{let z ← k a}[pk z]) :
    Pr{let x ← m >>= f}[pf x] ≤
      Pr{let y ← m >>= g}[pg y] + Pr{let z ← m >>= k}[pk z] := by
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete,
    prEvent_bind_eq_lintegral_of_discrete, ← lintegral_add_left Measurable.of_discrete]
  exact lintegral_mono hstep

theorem prEvent_bind_le_prEvent_add_two {α β γ δ ε : Type}
    (m : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
    (k : α → ProbComp δ) (h : α → ProbComp ε)
    (pf : β → Prop) (pg : γ → Prop) (pk : δ → Prop) (ph : ε → Prop)
    (hstep : ∀ a, Pr{let x ← f a}[pf x] ≤
      Pr{let y ← g a}[pg y] + Pr{let z ← k a}[pk z] + Pr{let w ← h a}[ph w]) :
    Pr{let x ← m >>= f}[pf x] ≤
      Pr{let y ← m >>= g}[pg y] + Pr{let z ← m >>= k}[pk z] +
      Pr{let w ← m >>= h}[ph w] := by
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete,
    prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete,
    ← lintegral_add_left Measurable.of_discrete, ← lintegral_add_left Measurable.of_discrete]
  exact lintegral_mono hstep

/-- One-sided identical-until-bad TV inequality: avoids paying `2×` on the dominant `121`-bit bad bound! -/
theorem measureETVDist_one_sided_with_slack {α : Type}
    (real₀ real₁ : ProbComp α) (flag₀ flag₁ : ProbComp (α × Bool))
    (badBound slackBound : ENNReal)
    (hlo₀ : ∀ p : α → Prop, Pr{let z ← flag₀}[p z.1 ∧ z.2 = false] ≤ Pr{let x ← real₀}[p x] + slackBound)
    (hhi₀ : ∀ p : α → Prop, Pr{let x ← real₀}[p x] ≤ Pr{let z ← flag₀}[p z.1 ∧ z.2 = false] + badBound + slackBound)
    (hlo₁ : ∀ p : α → Prop, Pr{let z ← flag₁}[p z.1 ∧ z.2 = false] ≤ Pr{let x ← real₁}[p x] + slackBound)
    (hhi₁ : ∀ p : α → Prop, Pr{let x ← real₁}[p x] ≤ Pr{let z ← flag₁}[p z.1 ∧ z.2 = false] + badBound + slackBound) :
    measureETVDist real₀ real₁ ≤ measureETVDist flag₀ flag₁ + badBound + 2 * slackBound := by
  refine iSup_le fun A => ?_
  have hrew (m : ProbComp α) : 𝒟[m] A.1 = Pr{let x ← m}[x ∈ A.1] := by
    have h := prEvent_eq_evalDist m (· ∈ A.1) A.2.mem
    rw [Set.ofPred_mem_eq] at h
    exact h.symm
  rw [hrew real₀, hrew real₁]
  have hdiff : ENNReal.absDiff
      (Pr{let z ← flag₀}[z.1 ∈ A.1 ∧ z.2 = false])
      (Pr{let z ← flag₁}[z.1 ∈ A.1 ∧ z.2 = false]) ≤ measureETVDist flag₀ flag₁ := by
    have h0 := prEvent_eq_evalDist_of_discrete flag₀ (fun z : α × Bool => z.1 ∈ A.1 ∧ z.2 = false)
    have h1 := prEvent_eq_evalDist_of_discrete flag₁ (fun z : α × Bool => z.1 ∈ A.1 ∧ z.2 = false)
    rw [h0, h1]
    exact measure_absDiff_apply_le_measureETVDist flag₀ flag₁ MeasurableSet.of_discrete
  obtain ⟨hd01, hd10⟩ := ENNReal.absDiff_le_iff.mp hdiff
  have htwo : 2 * slackBound = slackBound + slackBound := two_mul slackBound
  refine ENNReal.absDiff_le_iff.mpr ⟨?_, ?_⟩
  · calc
      Pr{let x ← real₀}[x ∈ A.1]
        ≤ Pr{let z ← flag₀}[z.1 ∈ A.1 ∧ z.2 = false] + badBound + slackBound := hhi₀ (· ∈ A.1)
      _ ≤ (Pr{let z ← flag₁}[z.1 ∈ A.1 ∧ z.2 = false] + measureETVDist flag₀ flag₁) + badBound + slackBound :=
          add_le_add (add_le_add hd01 le_rfl) le_rfl
      _ ≤ (Pr{let x ← real₁}[x ∈ A.1] + slackBound) + measureETVDist flag₀ flag₁ + badBound + slackBound :=
          add_le_add (add_le_add (add_le_add (hlo₁ (· ∈ A.1)) le_rfl) le_rfl) le_rfl
      _ = Pr{let x ← real₁}[x ∈ A.1] + (measureETVDist flag₀ flag₁ + badBound + 2 * slackBound) := by
          rw [htwo]; ring
  · calc
      Pr{let x ← real₁}[x ∈ A.1]
        ≤ Pr{let z ← flag₁}[z.1 ∈ A.1 ∧ z.2 = false] + badBound + slackBound := hhi₁ (· ∈ A.1)
      _ ≤ (Pr{let z ← flag₀}[z.1 ∈ A.1 ∧ z.2 = false] + measureETVDist flag₀ flag₁) + badBound + slackBound :=
          add_le_add (add_le_add hd10 le_rfl) le_rfl
      _ ≤ (Pr{let x ← real₀}[x ∈ A.1] + slackBound) + measureETVDist flag₀ flag₁ + badBound + slackBound :=
          add_le_add (add_le_add (add_le_add (hlo₀ (· ∈ A.1)) le_rfl) le_rfl) le_rfl
      _ = Pr{let x ← real₀}[x ∈ A.1] + (measureETVDist flag₀ flag₁ + badBound + 2 * slackBound) := by
          rw [htwo]; ring

theorem measureTVDist_one_sided_with_slack {α : Type}
    (real₀ real₁ : ProbComp α) (flag₀ flag₁ : ProbComp (α × Bool))
    (badBound slackBound : ENNReal) (hbad_fin : badBound ≠ ⊤) (hslack_fin : slackBound ≠ ⊤)
    (hlo₀ : ∀ p : α → Prop, Pr{let z ← flag₀}[p z.1 ∧ z.2 = false] ≤ Pr{let x ← real₀}[p x] + slackBound)
    (hhi₀ : ∀ p : α → Prop, Pr{let x ← real₀}[p x] ≤ Pr{let z ← flag₀}[p z.1 ∧ z.2 = false] + badBound + slackBound)
    (hlo₁ : ∀ p : α → Prop, Pr{let z ← flag₁}[p z.1 ∧ z.2 = false] ≤ Pr{let x ← real₁}[p x] + slackBound)
    (hhi₁ : ∀ p : α → Prop, Pr{let x ← real₁}[p x] ≤ Pr{let z ← flag₁}[p z.1 ∧ z.2 = false] + badBound + slackBound) :
    measureTVDist real₀ real₁ ≤ measureTVDist flag₀ flag₁ + badBound.toReal + 2 * slackBound.toReal := by
  have hetv := measureETVDist_one_sided_with_slack real₀ real₁ flag₀ flag₁ badBound slackBound hlo₀ hhi₀ hlo₁ hhi₁
  have hfin1 : measureETVDist flag₀ flag₁ + badBound ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measureETVDist_ne_top _ _, hbad_fin⟩
  have hfin2 : (2 : ENNReal) * slackBound ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hslack_fin
  have hfin : measureETVDist flag₀ flag₁ + badBound + 2 * slackBound ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hfin1, hfin2⟩
  rw [measureTVDist_eq_toReal_measureETVDist, measureTVDist_eq_toReal_measureETVDist]
  have hreal := ENNReal.toReal_mono hfin hetv
  rw [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_add (measureETVDist_ne_top _ _) hbad_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hreal
  exact hreal

private theorem flagged_step_support' (oracle : Oracle) (marked : World.Domain → Bool)
    (query : World.Domain) (state : Unit × Bool) (result : World.Range query × Unit × Bool)
    (reached : result ∈ support ((flaggedHandler oracle marked query).run state)) :
    result.2.2 = (state.2 || marked query) := by
  rw [flagged_handler_run] at reached
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨answer, _, rfl⟩ := reached
  rfl

private theorem flagged_step_monotone' (oracle : Oracle) (marked : World.Domain → Bool)
    (query : World.Domain) (state : Unit × Bool) (bad : state.2 = true)
    (result : World.Range query × Unit × Bool)
    (reached : result ∈ support ((flaggedHandler oracle marked query).run state)) :
    result.2.2 = true := by
  rw [flagged_step_support' oracle marked query state result reached, bad, Bool.true_or]

private theorem flagged_good_agree' (left right : Oracle) (marked : World.Domain → Bool)
    (agree : ∀ query, marked query = false → left.world query = right.world query)
    (query : World.Domain) (state : Unit × Bool) (_good : ¬state.2 = true)
    (event : World.Range query × Unit × Bool → Prop) :
    Pr{let result ← (flaggedHandler left marked query).run state}[
      event result ∧ ¬result.2.2 = true] =
    Pr{let result ← (flaggedHandler right marked query).run state}[
      event result ∧ ¬result.2.2 = true] := by
  cases hit : marked query with
  | false => rw [flagged_handler_run, flagged_handler_run, agree query hit]
  | true =>
    have zero (oracle : Oracle) :
        Pr{let result ← (flaggedHandler oracle marked query).run state}[
          event result ∧ ¬result.2.2 = true] = 0 := by
      apply prEvent_eq_zero_of_forall_mem_support
      intro result reached bad
      have flag := flagged_step_support' oracle marked query state result reached
      exact bad.2 (by simpa [hit] using flag)
    rw [zero left, zero right]

theorem flagged_run_good_and_bad_eq (left right : Oracle) (marked : World.Domain → Bool)
    (agree : ∀ query, marked query = false → left.world query = right.world query)
    {α : Type} (computation : OracleComp World α) :
    (∀ p : α → Prop,
      Pr{let r ← flaggedRun left marked computation}[p r.1 ∧ r.2.2 = false] =
      Pr{let r ← flaggedRun right marked computation}[p r.1 ∧ r.2.2 = false]) ∧
    Pr{let r ← flaggedRun left marked computation}[r.2.2 = true] =
    Pr{let r ← flaggedRun right marked computation}[r.2.2 = true] := by
  constructor
  · intro p
    have h := prEvent_simulateQ_run_and_not_bad_eq
      (flaggedHandler left marked) (flaggedHandler right marked) (fun s : Unit × Bool => s.2 = true)
      (flagged_good_agree' left right marked agree)
      (flagged_step_monotone' left marked) (flagged_step_monotone' right marked)
      computation ((), false) (fun r => p r.1)
    simpa only [flaggedRun, Bool.not_eq_true] using h
  · exact prEvent_simulateQ_run_bad_eq
      (flaggedHandler left marked) (flaggedHandler right marked) (fun s : Unit × Bool => s.2 = true)
      (flagged_good_agree' left right marked agree)
      (flagged_step_monotone' left marked) (flagged_step_monotone' right marked)
      computation ((), false)

theorem oracle_change_one_sided (left right : Oracle) (marked : World.Domain → Bool)
    (agree : ∀ query, marked query = false → left.world query = right.world query)
    {α : Type} (computation : OracleComp World α) (p : α → Prop) :
    Pr{let r ← flaggedRun left marked computation}[p r.1 ∧ r.2.2 = false] ≤
      Pr{let x ← fixedOracleRun right computation}[p x] ∧
    Pr{let x ← fixedOracleRun right computation}[p x] ≤
      Pr{let r ← flaggedRun left marked computation}[p r.1 ∧ r.2.2 = false] +
      Pr{let r ← flaggedRun left marked computation}[r.2.2 = true] := by
  obtain ⟨hgood, hbad⟩ := flagged_run_good_and_bad_eq left right marked agree computation
  have hproj : Pr{let x ← fixedOracleRun right computation}[p x] =
      Pr{let r ← flaggedRun right marked computation}[p r.1] := by
    rw [← flagged_run_projection right marked computation false, prEvent_map]
  have hsplit : Pr{let r ← flaggedRun right marked computation}[p r.1] =
      Pr{let r ← flaggedRun right marked computation}[p r.1 ∧ r.2.2 = true] +
      Pr{let r ← flaggedRun right marked computation}[p r.1 ∧ ¬(r.2.2 = true)] :=
    prEvent_eq_prEvent_and_add_prEvent_and_not _ _ _
  have hnot_eq : Pr{let r ← flaggedRun right marked computation}[p r.1 ∧ ¬(r.2.2 = true)] =
      Pr{let r ← flaggedRun left marked computation}[p r.1 ∧ r.2.2 = false] := by
    simpa only [Bool.not_eq_true] using (hgood p).symm
  rw [hproj, hsplit, hnot_eq]
  constructor
  · exact le_add_self
  · rw [add_comm]
    refine add_le_add le_rfl ?_
    calc
      Pr{let r ← flaggedRun right marked computation}[p r.1 ∧ r.2.2 = true]
        ≤ Pr{let r ← flaggedRun right marked computation}[r.2.2 = true] :=
          prEvent_mono _ _ _ (fun _ h => h.2)
      _ = Pr{let r ← flaggedRun left marked computation}[r.2.2 = true] := hbad.symm

/-- Pure `OracleComp` wrapper that tracks the exact same boolean query flag as `flaggedRun`,
preserving `PublicQueryBound` so `cached_chain3_distance` applies directly! -/
def flagComp (marked : World.Domain → Bool) {α : Type}
    (computation : OracleComp World α) : Bool → OracleComp World (α × Bool) :=
  OracleComp.recOn computation
    (fun value fl => pure (value, fl))
    (fun query _ ih fl =>
      (liftM (World.query query) : OracleComp World (World.Range query)) >>= fun answer =>
        ih answer (fl || marked query))

theorem flagComp_pure (marked : World.Domain → Bool) {α : Type} (value : α) (fl : Bool) :
    flagComp marked (pure value : OracleComp World α) fl = pure (value, fl) := rfl

theorem flagComp_query_bind (marked : World.Domain → Bool) {α : Type}
    (query : World.Domain) (next : World.Range query → OracleComp World α) (fl : Bool) :
    flagComp marked ((liftM (World.query query) : OracleComp World _) >>= next) fl =
      (liftM (World.query query) : OracleComp World _) >>= fun answer =>
        flagComp marked (next answer) (fl || marked query) := rfl

theorem flagComp_bound (marked : World.Domain → Bool) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) (fl : Bool) :
    PublicQueryBound (flagComp marked computation fl) budget := by
  induction computation using OracleComp.inductionOn generalizing budget fl with
  | pure _ => trivial
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rw [flagComp_query_bind]
    exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer) _⟩

theorem fixed_flagComp (oracle : Oracle) (marked : World.Domain → Bool) {α : Type}
    (computation : OracleComp World α) (fl : Bool) :
    fixedOracleRun oracle (flagComp marked computation fl) =
      (fun r : α × Unit × Bool => (r.1, r.2.2)) <$> flaggedRun oracle marked computation fl := by
  induction computation using OracleComp.inductionOn generalizing fl with
  | pure value =>
    rw [flagComp_pure, fixed_oracle_run_pure]
    simp [flaggedRun]
  | query_bind query next ih =>
    rw [flagComp_query_bind, flagged_run_query_bind, map_bind]
    have hstep : fixedOracleRun oracle ((liftM (World.query query) : OracleComp World _) >>= fun answer =>
          flagComp marked (next answer) (fl || marked query)) =
        oracle.world query >>= fun answer =>
          fixedOracleRun oracle (flagComp marked (next answer) (fl || marked query)) := by
      rw [fixed_run_eq_simulate, simulateQ_bind, simulateQ_query]
      simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map, ← fixed_run_eq_simulate]
    rw [hstep]
    exact bind_congr (fun answer => ih answer (fl || marked query))

/-! ### 4. 256-bit Chaining-Value Hiding for Leaf Calls 1..3 (Reused in Step 2) -/

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
  have hreord :
      𝒟[($ᵗ Digest) >>= fun salt => flaggedRun oracle (marksSalt salt) computation] =
      𝒟[do let traced ← fixedOracleRun oracle (traceCompression computation)
           let salt ← $ᵗ Digest
           pure (traced.1, (), traced.2.any (fun inp => decide (inp.extractLsb' 0 256 = salt)))] := by
    simp only [flagged_run_trace, Bool.false_or, map_eq_bind_pure_comp]
    exact evalDist_bind_comm_any ($ᵗ Digest) (fixedOracleRun oracle (traceCompression computation)) _
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

theorem leafCall0Input_tag (i : Index) (salt : Salt121) (val : Entry) :
    (leafCall0Input i salt val).extractLsb' 128 64 = leafTag i := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  unfold leafCall0Input
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true, Bool.true_and,
    show ¬ (128 + b < 128) by omega, ite_false, ite_true, show 128 + b - 128 = b by omega]

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

theorem cached_chain3_distance_discrete (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (val : Entry) {α : Type} [m : MeasurableSpace α] [DiscreteMeasurableSpace α]
    (next : Digest → OracleComp World α) (budget : Nat)
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
  have hm : m = ⊤ := by
    ext s
    exact ⟨fun _ => trivial, fun _ => MeasurableSet.of_discrete⟩
  subst hm
  exact cached_chain3_distance h768 permutation cache keys covered val next budget bounded

/-! ### 5. Lazy-ROM `CacheHitsPrefix` Bound (for 192-bit Tag+Salt Prefixes) -/

def CacheHitsPrefix (cache : CompressionCache) (prefixes : Finset (BitVec 192)) : Prop :=
  ∃ (k : BitVec COMPRESSION_INPUT_LENGTH) (ans : Digest),
    cache k = some ans ∧ ans.extractLsb' 0 192 ∈ prefixes

theorem CacheHitsPrefix.mono {cache : CompressionCache} {p1 p2 : Finset (BitVec 192)}
    (hsub : p1 ⊆ p2) (h : CacheHitsPrefix cache p1) : CacheHitsPrefix cache p2 :=
  let ⟨k, ans, hka, hm⟩ := h
  ⟨k, ans, hka, hsub hm⟩

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

/-! ### 6. Pure-Binary Bottom-Up Oracle Evaluation (`<= 83,886,079` Queries) -/

def HONEST_TREE_BUDGET : Nat := 4 * LENGTH + (LENGTH - 1)

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

def queryLeafOpened (h768 : COMPRESSION_INPUT_LENGTH = 768) (i : Index) (salt : Salt121) (val : Entry) :
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
    (i : Index) (salt : Salt121) (val : Entry) :
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
    (i : Index) (salt : Salt121) (val : Entry) :
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
        let raw ← leafFn ⟨n, h⟩
        pure (Function.update prev n (mask238 raw))
      else pure prev

def queryBinLevelAux (h768 : COMPRESSION_INPUT_LENGTH = 768) (prevLevel : Nat → Digest)
    (isRoot : Bool) : Nat → OracleComp World (Nat → Digest)
  | 0 => pure (fun _ => 0)
  | n + 1 => do
      let prev ← queryBinLevelAux h768 prevLevel isRoot n
      let raw ← queryCompress h768 (binaryInput (prevLevel (2 * n)) (prevLevel (2 * n + 1)))
      let d := if isRoot then raw else mask238 raw
      pure (Function.update prev n d)

def queryUpperLevels (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (l0 : Nat → Digest) : Nat → OracleComp World (Nat → Nat → Digest)
  | 0 => pure (fun l idx => if l = 0 then l0 idx else 0)
  | k + 1 => do
      let prev ← queryUpperLevels h768 l0 k
      let cur ← queryBinLevelAux h768 (prev k) (decide (k + 1 = 24)) (levelSize k / 2)
      pure (Function.update prev (k + 1) cur)

def queryTreeFromLeafFn (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (leafFn : Index → OracleComp World Digest) : OracleComp World (Nat → Nat → Digest) := do
  let l0 ← queryLevel0Aux leafFn LENGTH
  queryUpperLevels h768 l0 24

private theorem queryLevel0Aux_zero (leafFn : Index → OracleComp World Digest) :
    queryLevel0Aux leafFn 0 = pure (fun _ => 0) := rfl

private theorem queryLevel0Aux_succ (leafFn : Index → OracleComp World Digest) (n : Nat) :
    queryLevel0Aux leafFn (n + 1) = (do
      let prev ← queryLevel0Aux leafFn n
      if h : n < LENGTH then
        let raw ← leafFn ⟨n, h⟩
        pure (Function.update prev n (mask238 raw))
      else pure prev) := rfl

private theorem queryBinLevelAux_zero (h768 : COMPRESSION_INPUT_LENGTH = 768) (prevLevel : Nat → Digest)
    (isRoot : Bool) :
    queryBinLevelAux h768 prevLevel isRoot 0 = pure (fun _ => 0) := rfl

private theorem queryBinLevelAux_succ (h768 : COMPRESSION_INPUT_LENGTH = 768) (prevLevel : Nat → Digest)
    (isRoot : Bool) (n : Nat) :
    queryBinLevelAux h768 prevLevel isRoot (n + 1) = (do
      let prev ← queryBinLevelAux h768 prevLevel isRoot n
      let raw ← queryCompress h768 (binaryInput (prevLevel (2 * n)) (prevLevel (2 * n + 1)))
      let d := if isRoot then raw else mask238 raw
      pure (Function.update prev n d)) := rfl

private theorem queryUpperLevels_zero (h768 : COMPRESSION_INPUT_LENGTH = 768) (l0 : Nat → Digest) :
    queryUpperLevels h768 l0 0 = pure (fun l idx => if l = 0 then l0 idx else 0) := rfl

private theorem queryUpperLevels_succ (h768 : COMPRESSION_INPUT_LENGTH = 768) (l0 : Nat → Digest) (k : Nat) :
    queryUpperLevels h768 l0 (k + 1) = (do
      let prev ← queryUpperLevels h768 l0 k
      let cur ← queryBinLevelAux h768 (prev k) (decide (k + 1 = 24)) (levelSize k / 2)
      pure (Function.update prev (k + 1) cur)) := rfl

private theorem queryTreeFromLeafFn_def (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (leafFn : Index → OracleComp World Digest) :
    queryTreeFromLeafFn h768 leafFn = (do
      let l0 ← queryLevel0Aux leafFn LENGTH
      queryUpperLevels h768 l0 24) := rfl

attribute [irreducible] queryLevel0Aux queryBinLevelAux queryUpperLevels queryTreeFromLeafFn

private theorem sum_bin_calls_eq :
    (∑ k ∈ Finset.range 24, levelSize k / 2) = LENGTH - 1 := by
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
  have hbin : ∀ pl ir n, PublicQueryBound (queryBinLevelAux h768 pl ir n) n := by
    intro pl ir n; induction n with
    | zero => rw [queryBinLevelAux_zero]; exact public_query_bound_pure' _ _
    | succ n ih =>
      rw [queryBinLevelAux_succ]
      apply public_query_bound_bind ih
      intro _
      simpa only [Nat.add_zero] using public_query_bound_bind (queryCompress_bound h768 _) (fun _ => public_query_bound_pure' _ 0)
  have hup : ∀ l0 k, PublicQueryBound (queryUpperLevels h768 l0 k) (∑ j ∈ Finset.range k, levelSize j / 2) := by
    intro l0 k; induction k with
    | zero =>
      rw [queryUpperLevels_zero]
      simp only [Finset.range_zero, Finset.sum_empty]
      exact public_query_bound_pure' _ _
    | succ k ih =>
      rw [queryUpperLevels_succ, Finset.sum_range_succ]
      apply public_query_bound_bind ih
      intro prev
      simpa only [Nat.add_zero] using public_query_bound_bind (hbin _ _ _) (fun _ => public_query_bound_pure' _ 0)
  rw [queryTreeFromLeafFn_def]
  unfold HONEST_TREE_BUDGET
  refine public_query_bound_bind (hl0 LENGTH) fun l0 => ?_
  rw [← sum_bin_calls_eq]
  exact hup l0 24

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
        refine ⟨Function.update f n (mask238 (leaves ⟨n, hn⟩)), rfl, ?_⟩
        intro idx hlt hlen
        by_cases heq : idx = n
        · subst heq; simp [nodeValFromLeaves, hn, maskLevel]
        · rw [Function.update_of_ne heq]; exact hval idx (by omega) hlen
      · rw [dif_neg hn, fixed_oracle_run_pure]
        exact ⟨f, rfl, fun idx hlt hlen => hval idx (by omega) hlen⟩
  obtain ⟨l0, hl0_run, hl0_val⟩ := hl0 LENGTH
  have hl0_all : ∀ idx < levelSize 0, l0 idx = nodeValFromLeaves c leaves 0 idx :=
    fun idx h => hl0_val idx (by rwa [levelSize_0, show (16777216 : Nat) = LENGTH by decide] at h)
      (by rwa [levelSize_0, show (16777216 : Nat) = LENGTH by decide] at h)
  have hbin : ∀ (prevLvl : Nat) (hlt24 : prevLvl < 24)
      (prevArr : Nat → Digest) (hprev : ∀ idx < levelSize prevLvl, prevArr idx = nodeValFromLeaves c leaves prevLvl idx)
      (n : Nat) (hn : n ≤ levelSize prevLvl / 2),
      ∃ f, fixedOracleRun oracle (queryBinLevelAux h768 prevArr (decide (prevLvl + 1 = 24)) n) = pure f ∧
        (∀ idx < n, f idx = nodeValFromLeaves c leaves (prevLvl + 1) idx) := by
    intro prevLvl hlt24 prevArr hprev n hn
    induction n with
    | zero =>
      rw [queryBinLevelAux_zero]
      exact ⟨fun _ => 0, fixed_oracle_run_pure _ _, fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ n ih =>
      obtain ⟨f, hrun, hval⟩ := ih (by omega)
      rw [queryBinLevelAux_succ, fixed_oracle_run_bind, hrun, pure_bind, fixed_oracle_run_bind,
        queryCompress_fixed, pure_bind, fixed_oracle_run_pure]
      refine ⟨Function.update f n _, rfl, ?_⟩
      intro idx hlt
      by_cases heq : idx = n
      · subst heq
        have hev := levelSize_even prevLvl hlt24
        have hpair : 2 * idx + 1 < levelSize prevLvl := by omega
        simp only [Function.update_self, nodeValFromLeaves, hpair, ite_true, maskLevel, decide_eq_true_eq]
        rw [hprev (2 * idx) (by omega), hprev (2 * idx + 1) (by omega)]
      · rw [Function.update_of_ne heq]; exact hval idx (by omega)
  have hup : ∀ k ≤ 24, ∃ arr, fixedOracleRun oracle (queryUpperLevels h768 l0 k) = pure arr ∧
      ∀ l ≤ k, ∀ idx < levelSize l, arr l idx = nodeValFromLeaves c leaves l idx := by
    intro k hk; induction k with
    | zero =>
      rw [queryUpperLevels_zero]
      refine ⟨_, fixed_oracle_run_pure _ _, ?_⟩
      intro l hl idx hidx
      have hl0' : l = 0 := by omega
      subst hl0'
      simp only [ite_true]
      exact hl0_all idx hidx
    | succ k ih =>
      obtain ⟨arr, hrun, hval⟩ := ih (by omega)
      rw [queryUpperLevels_succ, fixed_oracle_run_bind, hrun, pure_bind]
      obtain ⟨cur, hcur_run, hcur_lt⟩ := hbin k (by omega)
        (arr k) (hval k (le_refl _)) (levelSize k / 2) (le_refl _)
      rw [fixed_oracle_run_bind, hcur_run, pure_bind, fixed_oracle_run_pure]
      refine ⟨Function.update arr (k + 1) cur, rfl, ?_⟩
      intro l hl idx hidx
      by_cases hltop : l = k + 1
      · subst hltop
        rw [Function.update_self]
        rw [levelSize_step k (by omega)] at hidx
        exact hcur_lt idx hidx
      · rw [Function.update_of_ne hltop]
        exact hval l (by omega) idx hidx
  obtain ⟨nodes, hup_run, hup_val⟩ := hup 24 (le_refl _)
  rw [queryTreeFromLeafFn_def, fixed_oracle_run_bind, hl0_run, pure_bind, hup_run]
  exact ⟨nodes, rfl, hup_val⟩

/-! ### 7. Pure `GoodIdeal0Trace` Invariant for `queryIdeal0Tree` -/

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
    (sOpen : Index → Salt121) (cv0 : Index → Digest) (positions : Positions) (i : Index) :
    OracleComp World Digest :=
  if i ∈ positions then queryLeafOpened h768 i (sOpen i) (msg i)
  else queryLeafFromCv0 h768 (cv0 i) (msg i)

/-- Every compression query executed during `queryTreeFromLeafFn (ideal0LeafFn ...)`
satisfies `GoodIdeal0Trace`: its low 192 bits either carry an opened leaf tag, a `cv0 i` prefix,
or an earlier compression output from the same trace. -/
theorem queryIdeal0Tree_good_trace (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (sOpen : Index → Salt121) (cv0 : Index → Digest)
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
        refine ⟨Function.update f n (mask238 d), tr ++ trd, rfl, ?_, ?_⟩
        · intro p hp
          rcases List.mem_append.mp hp with hp1 | hp2
          · exact good_query_mono (fun q hq => List.mem_append_left _ hq) (hgood p hp1)
          · exact good_query_mono (fun q hq => List.mem_append_right _ hq) (hdgood p hp2)
        · intro idx hlt hlen
          by_cases heq : idx = n
          · subst heq; rw [Function.update_self, extractLsb'_192_mask238]
            obtain ⟨p, hp, hpeq⟩ := hdp
            exact ⟨p, List.mem_append_right _ hp, hpeq⟩
          · rw [Function.update_of_ne heq]
            obtain ⟨p, hp, hpeq⟩ := hnodes idx (by omega) hlen
            exact ⟨p, List.mem_append_left _ hp, hpeq⟩
      · rw [dif_neg hn]
        simp only [traceReplies_pure, fixed_oracle_run_pure, pure_bind, List.append_nil]
        exact ⟨f, tr, rfl, hgood, fun idx hlt hlen => hnodes idx (by omega) hlen⟩
  obtain ⟨l0, tr0, htr0_run, htr0_good, htr0_nodes⟩ := hl0 LENGTH
  have hbin : ∀ (prevTr : CompressionReplies) (hpg : GoodIdeal0Trace positions cv0 prevTr)
      (prevArr : Nat → Digest) (ps : Nat) (ir : Bool)
      (hprev : ∀ idx < ps, ∃ p ∈ prevTr, (prevArr idx).extractLsb' 0 192 = p.2.extractLsb' 0 192)
      (n : Nat) (hn : 2 * n ≤ ps),
      ∃ f tr,
        fixedOracleRun oracle (traceCompressionReplies (queryBinLevelAux h768 prevArr ir n)) = pure (f, tr) ∧
        GoodIdeal0Trace positions cv0 (prevTr ++ tr) ∧
        (∀ idx < n, ∃ p ∈ prevTr ++ tr, (f idx).extractLsb' 0 192 = p.2.extractLsb' 0 192) := by
    intro prevTr hpg prevArr ps ir hprev n hn
    induction n with
    | zero =>
      exact ⟨fun _ => 0, [],
        by simp only [queryBinLevelAux_zero, traceReplies_pure, fixed_oracle_run_pure],
        by simpa using hpg, fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ n ih =>
      obtain ⟨f, tr, hrun, hgood, hval⟩ := ih (by omega)
      rw [queryBinLevelAux_succ]
      let x := (binaryInput (prevArr (2 * n)) (prevArr (2 * n + 1))).cast h768.symm
      let raw : Digest := oracle.compression x
      let d : Digest := if ir then raw else mask238 raw
      have hrunb :
          fixedOracleRun oracle (traceCompressionReplies (do
            let prev ← queryBinLevelAux h768 prevArr ir n
            let raw' ← queryCompress h768 (binaryInput (prevArr (2 * n)) (prevArr (2 * n + 1)))
            let d' := if ir then raw' else mask238 raw'
            pure (Function.update prev n d'))) =
          pure (Function.update f n d, tr ++ [(x, raw)]) := by
        simp only [traceReplies_bind, traceReplies_pure, fixed_oracle_run_bind, fixed_oracle_run_pure,
          traceReplies_queryCompress_fixed, hrun, pure_bind, List.append_nil]
        rfl
      refine ⟨Function.update f n d, tr ++ [(x, raw)], hrunb, ?_, ?_⟩
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
          · exact extractLsb'_192_mask238 raw
          · rfl
        · rw [Function.update_of_ne heq]
          obtain ⟨p, hp, hpeq⟩ := hval idx (by omega)
          refine ⟨p, ?_, hpeq⟩
          rcases List.mem_append.mp hp with h1 | h2
          · exact List.mem_append_left _ h1
          · exact List.mem_append_right _ (List.mem_append_left _ h2)
  have hup : ∀ k ≤ 24, ∃ arr tr,
      fixedOracleRun oracle (traceCompressionReplies (queryUpperLevels h768 l0 k)) = pure (arr, tr) ∧
      GoodIdeal0Trace positions cv0 (tr0 ++ tr) ∧
      ∀ l ≤ k, ∀ idx < levelSize l, ∃ p ∈ tr0 ++ tr, (arr l idx).extractLsb' 0 192 = p.2.extractLsb' 0 192 := by
    intro k hk; induction k with
    | zero =>
      refine ⟨fun l idx => if l = 0 then l0 idx else 0, [],
        by simp only [queryUpperLevels_zero, traceReplies_pure, fixed_oracle_run_pure], by simpa using htr0_good, ?_⟩
      intro l hl idx hidx
      have hl0' : l = 0 := by omega
      subst hl0'
      simp only [List.append_nil, ite_true]
      have hidx' : idx < LENGTH := by rwa [levelSize_0, show (16777216 : Nat) = LENGTH by decide] at hidx
      exact htr0_nodes idx hidx' hidx'
    | succ k ih =>
      obtain ⟨arr, tr, hrun, hgood, hval⟩ := ih (by omega)
      rw [queryUpperLevels_succ, traceReplies_bind, fixed_oracle_run_bind, hrun, pure_bind]
      dsimp only
      have hev := levelSize_even k (by omega)
      obtain ⟨cur, trc, hcrun, hcgood, hclt⟩ := hbin (tr0 ++ tr) hgood
        (arr k) (levelSize k) (decide (k + 1 = 24)) (hval k (le_refl _))
        (levelSize k / 2) (by omega)
      simp only [traceReplies_bind, traceReplies_pure, fixed_oracle_run_bind, fixed_oracle_run_pure,
        hcrun, pure_bind, List.append_nil]
      refine ⟨Function.update arr (k + 1) cur, tr ++ trc, rfl, ?_, ?_⟩
      · simpa [List.append_assoc] using hcgood
      · intro l hl idx hidx
        by_cases htop : l = k + 1
        · subst htop; rw [Function.update_self]
          rw [levelSize_step k (by omega)] at hidx
          simpa [List.append_assoc] using hclt idx hidx
        · rw [Function.update_of_ne htop]
          obtain ⟨p, hp, hpeq⟩ := hval l (by omega) idx hidx
          refine ⟨p, ?_, hpeq⟩
          rw [← List.append_assoc]
          exact List.mem_append_left _ hp
  obtain ⟨nodes, trUp, hup_run, hup_good, _⟩ := hup 24 (le_refl _)
  rw [queryTreeFromLeafFn_def, traceReplies_bind, fixed_oracle_run_bind, htr0_run, pure_bind]
  dsimp only
  rw [fixed_oracle_run_bind, hup_run, pure_bind, fixed_oracle_run_pure]
  exact ⟨nodes, tr0 ++ trUp, rfl, hup_good⟩

end CommitGolfCandidate
