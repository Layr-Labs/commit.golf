import CommitGolfCandidate.HidingReprogram
import CommitGolfCandidate.HidingQueries

/-! Record the compression inputs chosen by an adaptive computation. Under the
unprogrammed oracle this trace does not depend on a separately sampled hidden
salt. This is the independence needed to bound reprogramming detection. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

def compressionHead : World.Domain → List (BitVec COMPRESSION_INPUT_LENGTH)
  | .inr (.inl input) => [input]
  | _ => []

/-- Forward every real query and retain only compression inputs, in query order. -/
def traceCompression {α : Type} (computation : OracleComp World α) :
    OracleComp World (α × List (BitVec COMPRESSION_INPUT_LENGTH)) :=
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

theorem fixed_run_query_bind (oracle : Oracle) {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) :
    fixedOracleRun oracle ((liftM (World.query query) : OracleComp World _) >>= next) =
      (oracle.world query >>= fun answer => fixedOracleRun oracle (next answer)) := by
  simp only [fixed_run_eq_simulate, simulateQ_bind, simulateQ_query,
    OracleQuery.input_query, OracleQuery.cont_query, id_map]

theorem trace_run_query_bind (oracle : Oracle) {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) :
    fixedOracleRun oracle
      (traceCompression ((liftM (World.query query) : OracleComp World _) >>= next)) =
      (do let answer ← oracle.world query
          let result ← fixedOracleRun oracle (traceCompression (next answer))
          pure (result.1, compressionHead query ++ result.2)) := by
  rw [trace_compression_query_bind, fixed_run_query_bind]
  apply bind_congr
  intro answer
  rw [fixed_oracle_run_bind]
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
    (result : α × List (BitVec COMPRESSION_INPUT_LENGTH))
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

/-- The marker is exactly membership of the salt among low halves of traced inputs. -/
theorem flagged_run_trace (oracle : Oracle) (salt : BitVec 256) {α : Type}
    (computation : OracleComp World α) (flag : Bool) :
    flaggedRun oracle (marksSalt salt) computation flag =
      ((fun result : α × List (BitVec COMPRESSION_INPUT_LENGTH) =>
        (result.1, (), flag || result.2.any (fun input => decide (input.extractLsb' 0 256 = salt)))) <$>
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
    have head : (compressionHead query).any (fun input => decide (input.extractLsb' 0 256 = salt)) =
        marksSalt salt query := by
      rcases query with coins | publicQuery
      · rfl
      · rcases publicQuery with input | permQuery
        · change (decide (input.extractLsb' 0 256 = salt) || false) = _
          exact Bool.or_false _
        · rcases permQuery <;> rfl
    simp only [List.any_append, head, Bool.or_assoc]

end CommitGolfCandidate
