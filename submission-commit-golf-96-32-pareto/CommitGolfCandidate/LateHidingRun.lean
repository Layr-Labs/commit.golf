import CommitGolfCandidate.Probability
import CommitGolfCandidate.LateModel
import CommitGolfCandidate.CompressionSampling
import CommitGolfCandidate.HidingQueries
import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad

/-! Oracle-run lemmas for the late-salt hiding proof.

These are the scheme-independent parts of the base tree's hiding framework
(dadon's c9b8af82: `HidingDistribution`, `HidingReprogram`, `HidingTrace`,
`HidingHiddenQuery`, `HidingCache`, `HidingStages`), proved again here so that the late-salt proof
imports nothing that depends on a particular machine image. The marker for
reprogrammed inputs is an arbitrary predicate on compression inputs, and the
staged sampling lemma starts from an arbitrary cache. -/
namespace CommitGolfCandidate.LateHiding

-- Observations retain the discrete measurable structure used by the contract.
local instance runDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling
open OracleComp.ProgramLogic.Relational

/-! ### Fixed-oracle execution -/

theorem run_bind (oracle : Oracle) {α β : Type}
    (computation : OracleComp World α) (next : α → OracleComp World β) :
    fixedOracleRun oracle (computation >>= next) =
      (fixedOracleRun oracle computation >>= fun value => fixedOracleRun oracle (next value)) := by
  simp only [fixedOracleRun, oracle_run_bind, map_bind, map_pure, bind_map_left]
  simp only [map_eq_bind_pure_comp]
  apply bind_congr
  intro first
  cases first
  apply bind_congr
  intro second
  cases second
  rfl

theorem run_map (oracle : Oracle) {α β : Type}
    (f : α → β) (computation : OracleComp World α) :
    fixedOracleRun oracle (f <$> computation) = f <$> fixedOracleRun oracle computation := by
  simp only [fixedOracleRun, oracle_run_map, Functor.map_map]

theorem run_coins (oracle : Oracle) {α : Type} (coins : ProbComp α) :
    fixedOracleRun oracle (liftM coins : OracleComp World α) = coins := by
  rw [fixedOracleRun, oracle_run_coins, Functor.map_map]
  exact id_map coins

theorem run_coins_bind (oracle : Oracle) {α β : Type} (coins : ProbComp α)
    (next : α → OracleComp World β) :
    fixedOracleRun oracle ((liftM coins : OracleComp World α) >>= next) =
      (coins >>= fun value => fixedOracleRun oracle (next value)) := by
  rw [run_bind, run_coins]

/-- One compression call under a fixed oracle is a table lookup. -/
theorem run_compress (oracle : Oracle) {α : Type} (input : Late.Block)
    (next : Late.Digest → OracleComp World α) :
    fixedOracleRun oracle
      ((liftM (World.query (.inr (.inl input))) : OracleComp World Late.Digest) >>= next) =
      fixedOracleRun oracle (next (oracle.compression input)) :=
  fixed_oracle_run_public oracle (.inl input) next

theorem run_eq_simulate (oracle : Oracle) {α : Type} (computation : OracleComp World α) :
    fixedOracleRun oracle computation = simulateQ oracle.world computation := by
  exact QueryImpl.fst_map_run_withCost oracle.world
    (fun query => Multiplicative.ofAdd (Oracle.callCost query)) computation

theorem run_query_bind (oracle : Oracle) {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) :
    fixedOracleRun oracle ((liftM (World.query query) : OracleComp World _) >>= next) =
      (oracle.world query >>= fun answer => fixedOracleRun oracle (next answer)) := by
  simp only [run_eq_simulate, simulateQ_bind, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, id_map]

/-! ### Flagged execution and oracle change -/

/-- Forward the actual oracle replies and remember whether a marked query occurred.
The flag is proof instrumentation, never an answer exposed to the computation. -/
def flaggedHandler (oracle : Oracle) (marked : World.Domain → Bool) :
    QueryImpl World (StateT (Unit × Bool) ProbComp) :=
  fun query state => do
    let answer ← oracle.world query
    pure (answer, (state.1, state.2 || marked query))

def flaggedRun (oracle : Oracle) (marked : World.Domain → Bool) {α : Type}
    (computation : OracleComp World α) (flag : Bool := false) : ProbComp (α × Unit × Bool) :=
  (simulateQ (flaggedHandler oracle marked) computation).run ((), flag)

theorem flagged_handler_run (oracle : Oracle) (marked : World.Domain → Bool)
    (query : World.Domain) (state : Unit × Bool) :
    (flaggedHandler oracle marked query).run state =
      (do let answer ← oracle.world query
          pure (answer, (state.1, state.2 || marked query))) := rfl

private theorem flagged_step_support (oracle : Oracle) (marked : World.Domain → Bool)
    (query : World.Domain) (state : Unit × Bool) (result : World.Range query × Unit × Bool)
    (reached : result ∈ support ((flaggedHandler oracle marked query).run state)) :
    result.2.2 = (state.2 || marked query) := by
  rw [flagged_handler_run] at reached
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨answer, _, rfl⟩ := reached
  rfl

private theorem flagged_step_monotone (oracle : Oracle) (marked : World.Domain → Bool)
    (query : World.Domain) (state : Unit × Bool) (bad : state.2 = true)
    (result : World.Range query × Unit × Bool)
    (reached : result ∈ support ((flaggedHandler oracle marked query).run state)) :
    result.2.2 = true := by
  rw [flagged_step_support oracle marked query state result reached, bad, Bool.true_or]

private theorem flagged_good_agree (left right : Oracle) (marked : World.Domain → Bool)
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
      have flag := flagged_step_support oracle marked query state result reached
      exact bad.2 (by simpa [hit] using flag)
    rw [zero left, zero right]

private theorem flagged_projection (oracle : Oracle) (marked : World.Domain → Bool)
    {α : Type} (computation : OracleComp World α) (state : Unit × Bool) :
    Prod.fst <$> (simulateQ (flaggedHandler oracle marked) computation).run state =
      simulateQ oracle.world computation := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, flagged_handler_run,
      map_bind, bind_assoc, pure_bind, ih]

/-- Erasing the proof-only flag recovers exactly the original execution. -/
theorem flagged_run_projection (oracle : Oracle) (marked : World.Domain → Bool)
    {α : Type} (computation : OracleComp World α) (flag : Bool) :
    Prod.fst <$> flaggedRun oracle marked computation flag = fixedOracleRun oracle computation := by
  rw [run_eq_simulate]
  exact flagged_projection oracle marked computation ((), flag)

/-- Any two fixed oracle realizations agreeing outside marked queries are close
up to the probability of making such a query. The adversary need not be deterministic. -/
theorem change_distance_le_hit (left right : Oracle) (marked : World.Domain → Bool)
    (agree : ∀ query, marked query = false → left.world query = right.world query)
    {α : Type} (computation : OracleComp World α) :
    measureTVDist (fixedOracleRun left computation) (fixedOracleRun right computation) ≤
      (prEvent ((fun result => result.2.2 = true) <$> (flaggedRun left marked computation))).toReal := by
  let : MeasurableSpace (α × Unit × Bool) := ⊤
  have joint := measureETVDist_simulateQ_run_le_prEvent_bad
    (flaggedHandler left marked) (flaggedHandler right marked) (fun state => state.2 = true)
    (flagged_good_agree left right marked agree)
    (flagged_step_monotone left marked) (flagged_step_monotone right marked)
    computation ((), false)
  have projected := measureTVDist_map_le
    (flaggedRun left marked computation) (flaggedRun right marked computation)
    Prod.fst Measurable.of_discrete
  rw [flagged_run_projection, flagged_run_projection] at projected
  exact projected.trans (ENNReal.toReal_mono (prEvent_ne_top _) joint)

/-- Mark the compression inputs selected by `hit`; no other query is marked. -/
def marksInput (hit : Late.Block → Bool) : World.Domain → Bool
  | .inr (.inl input) => hit input
  | _ => false

/-- Update one compression cell; permutation and inverse remain exactly the same. -/
def programCompression (oracle : Oracle) (input : Late.Block) (answer : Late.Digest) : Oracle :=
  ⟨Function.update oracle.compression input answer, oracle.permutation⟩

theorem program_compression_agrees (oracle : Oracle) (input : Late.Block) (answer : Late.Digest)
    (hit : Late.Block → Bool) (selected : hit input = true)
    (query : World.Domain) (unmarked : marksInput hit query = false) :
    oracle.world query = (programCompression oracle input answer).world query := by
  rcases query with coins | publicQuery
  · rfl
  · rcases publicQuery with requested | permQuery
    · have different : requested ≠ input := by
        intro same
        subst requested
        simp [marksInput, selected] at unmarked
      simp only [Oracle.world, Oracle.answer, programCompression, QueryImpl.add_apply_inr,
        pure_inj]
      exact (Function.update_of_ne different answer oracle.compression).symm
    · rcases permQuery with forward | inverse <;> rfl

/-- Concrete reprogramming loss, charged against the original unprogrammed run. -/
theorem reprogram_compression_distance (oracle : Oracle) (input : Late.Block) (answer : Late.Digest)
    (hit : Late.Block → Bool) (selected : hit input = true)
    {α : Type} (computation : OracleComp World α) :
    measureTVDist (fixedOracleRun oracle computation)
      (fixedOracleRun (programCompression oracle input answer) computation) ≤
      (prEvent ((fun result => result.2.2 = true) <$>
        (flaggedRun oracle (marksInput hit) computation))).toReal :=
  change_distance_le_hit oracle (programCompression oracle input answer) _
    (program_compression_agrees oracle input answer hit selected) computation

/-! ### Compression traces -/

def compressionHead : World.Domain → List Late.Block
  | .inr (.inl input) => [input]
  | _ => []

/-- Forward every real query and retain only compression inputs, in query order. -/
def traceCompression {α : Type} (computation : OracleComp World α) :
    OracleComp World (α × List Late.Block) :=
  OracleComp.recOn computation
    (fun value => pure (value, []))
    (fun query _ next => do
      let answer ← (liftM (World.query query) : OracleComp World _)
      let (value, trace) ← next answer
      pure (value, compressionHead query ++ trace))

theorem trace_compression_pure {α : Type} (value : α) :
    traceCompression (pure value : OracleComp World α) = pure (value, []) := rfl

theorem trace_compression_query_bind {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) :
    traceCompression ((liftM (World.query query) : OracleComp World _) >>= next) =
      (do let answer ← (liftM (World.query query) : OracleComp World _)
          let (value, trace) ← traceCompression (next answer)
          pure (value, compressionHead query ++ trace)) := rfl

theorem trace_run_query_bind (oracle : Oracle) {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) :
    fixedOracleRun oracle
      (traceCompression ((liftM (World.query query) : OracleComp World _) >>= next)) =
      (do let answer ← oracle.world query
          let result ← fixedOracleRun oracle (traceCompression (next answer))
          pure (result.1, compressionHead query ++ result.2)) := by
  rw [trace_compression_query_bind, run_query_bind]
  apply bind_congr
  intro answer
  rw [run_bind]
  apply bind_congr
  intro result
  cases result
  exact fixed_oracle_run_pure _ _

private theorem compression_head_cost (query : World.Domain) :
    (compressionHead query).length ≤ Oracle.callCost query := by
  rcases query with coins | publicQuery
  · exact Nat.le_refl 0
  · rcases publicQuery with input | permQuery
    · exact Nat.le_refl 1
    · exact Nat.zero_le _

/-- The trace length is bounded by the contract's public-query budget, even with
arbitrarily many private coin requests and arbitrary fixed permutation replies. -/
theorem trace_run_length (oracle : Oracle) {α : Type} (computation : OracleComp World α)
    (budget : Nat) (bounded : PublicQueryBound computation budget)
    (result : α × List Late.Block)
    (reached : result ∈ support (fixedOracleRun oracle (traceCompression computation))) :
    result.2.length ≤ budget := by
  induction computation using OracleComp.inductionOn generalizing budget result with
  | pure value =>
    rw [trace_compression_pure, fixed_oracle_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact Nat.zero_le _
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget-Oracle.callCost query)) at bounded
    rw [trace_run_query_bind] at reached
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
    obtain ⟨answer, _, tail, tailReached, rfl⟩ := reached
    have rest := ih answer (budget-Oracle.callCost query) (bounded.2 answer) tail tailReached
    have head := compression_head_cost query
    simp only [List.length_append]
    omega

theorem flagged_run_query_bind (oracle : Oracle) (marked : World.Domain → Bool)
    {α : Type} (query : World.Domain) (next : World.Range query → OracleComp World α) (flag : Bool) :
    flaggedRun oracle marked ((liftM (World.query query) : OracleComp World _) >>= next) flag =
      (oracle.world query >>= fun answer => flaggedRun oracle marked (next answer) (flag || marked query)) := by
  simp only [flaggedRun, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
    OracleQuery.cont_query, id_map, StateT.run_bind, flagged_handler_run, bind_assoc, pure_bind]

/-- The flag is exactly whether a traced compression input is selected. -/
theorem flagged_run_trace (oracle : Oracle) (hit : Late.Block → Bool) {α : Type}
    (computation : OracleComp World α) (flag : Bool) :
    flaggedRun oracle (marksInput hit) computation flag =
      ((fun result : α × List Late.Block => (result.1, (), flag || result.2.any hit)) <$>
        fixedOracleRun oracle (traceCompression computation)) := by
  induction computation using OracleComp.inductionOn generalizing flag with
  | pure value =>
    simp only [flaggedRun, simulateQ_pure, StateT.run_pure, trace_compression_pure,
      fixed_oracle_run_pure, map_pure, List.any_nil, Bool.or_false]
  | query_bind query next ih =>
    rw [flagged_run_query_bind, trace_run_query_bind, map_bind]
    apply bind_congr
    intro answer
    rw [ih]
    simp only [bind_pure_comp, Functor.map_map]
    apply congrArg (fun f => f <$> fixedOracleRun oracle (traceCompression (next answer)))
    funext result
    have head : (compressionHead query).any hit = marksInput hit query := by
      rcases query with coins | publicQuery
      · rfl
      · rcases publicQuery with input | permQuery
        · change (hit input || false) = _
          exact Bool.or_false _
        · rcases permQuery <;> rfl
    simp only [List.any_append, head, Bool.or_assoc]

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

/-! ### Lazy prefixes and caches -/

/-- The cache runner respects monadic sequencing, retaining the intermediate cache. -/
theorem lazy_run_bind (permutation : Perm) {α β : Type} (first : OracleComp World α)
    (next : α → OracleComp World β) (cache : CompressionCache) :
    compressionRun permutation (first >>= next) cache = (do
      let (value, after) ← compressionRun permutation first cache
      compressionRun permutation (next value) after) := by
  simp [compressionRun, simulateQ_bind, StateT.run_bind]

/-- After any prefix run lazily from `cache`, resample only the cells not fixed by
its transcript. This preserves the exact distribution of every continuation. -/
theorem staged_sampling (permutation : Perm) (cache : CompressionCache) {α β : Type}
    (first : OracleComp World α) (next : α → OracleComp World β) :
    𝒟[do let table ← $ᵗ Compression
         fixedOracleRun ⟨tableExtending cache table, permutation⟩ (first >>= next)] =
    𝒟[do let result ← compressionRun permutation first cache
         let table ← $ᵗ Compression
         fixedOracleRun ⟨tableExtending result.2 table, permutation⟩ (next result.1)] := by
  rw [← compression_sampling_equivalence, lazy_run_bind, map_bind]
  apply _root_.evalDist_bind_congr
  intro result
  cases result with
  | mk value after => exact compression_sampling_equivalence permutation (next value) after

/-- A public-query budget bounds the number of populated compression inputs in
every reachable cache. Permutation queries can only reduce the available budget. -/
theorem cache_covered (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) (cache : CompressionCache)
    (known : Finset Late.Block) (covered : ∀ key, cache key ≠ none → key ∈ known)
    (result : α × CompressionCache)
    (reached : result ∈ support (compressionRun permutation computation cache)) :
    ∃ keys : Finset Late.Block, keys.card ≤ known.card + budget ∧
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
      have tails : ∀ answer, PublicQueryBound (next answer) (budget-1) := bounded.2
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress] at reached
        cases cached : cache input with
        | some answer =>
          rw [cached] at reached
          obtain ⟨keys, size, covers⟩ := ih answer (budget-1) (tails answer) cache known covered result reached
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
          obtain ⟨keys, size, covers⟩ := ih answer (budget-1) (tails answer)
            (cache.cacheQuery input answer) (insert input known) nextCovered result reached
          have inserted := Finset.card_insert_le input known
          exact ⟨keys, by omega, covers⟩
      · rcases permQuery with input | input
        · rw [compression_run_permute] at reached
          obtain ⟨keys, size, covers⟩ := ih _ (budget-1) (tails _) cache known covered result reached
          exact ⟨keys, by omega, covers⟩
        · rw [compression_run_inverse] at reached
          obtain ⟨keys, size, covers⟩ := ih _ (budget-1) (tails _) cache known covered result reached
          exact ⟨keys, by omega, covers⟩

/-- In particular the first stage starts with no preloaded compression answers. -/
theorem first_stage_cache_bound (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) (result : α × CompressionCache)
    (reached : result ∈ support (compressionRun permutation computation ∅)) :
    ∃ keys : Finset Late.Block, keys.card ≤ budget ∧
      ∀ key, result.2 key ≠ none → key ∈ keys := by
  have result := cache_covered permutation computation budget bounded ∅ ∅
    (by simp) result reached
  simpa only [Finset.card_empty, Nat.zero_add] using result

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

end CommitGolfCandidate.LateHiding
