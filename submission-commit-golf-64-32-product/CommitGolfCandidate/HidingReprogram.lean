import CommitGolfCandidate.HidingDistribution
import VCVio.ProgramLogic.Relational.SimulateQ.UntilBad

/-! Changing an oracle at hidden inputs is detectable only after querying one of
those inputs. These lemmas retain private coins and both permutation directions;
the distinguishing bound applies to arbitrary adaptive oracle computations. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingReprogramDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.ProgramLogic.Relational

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

theorem fixed_run_eq_simulate (oracle : Oracle) {α : Type} (computation : OracleComp World α) :
    fixedOracleRun oracle computation = simulateQ oracle.world computation := by
  exact QueryImpl.fst_map_run_withCost oracle.world
    (fun query => Multiplicative.ofAdd (Oracle.callCost query)) computation

/-- Erasing the proof-only flag recovers exactly the original execution. -/
theorem flagged_run_projection (oracle : Oracle) (marked : World.Domain → Bool)
    {α : Type} (computation : OracleComp World α) (flag : Bool) :
    Prod.fst <$> flaggedRun oracle marked computation flag = fixedOracleRun oracle computation := by
  rw [fixed_run_eq_simulate]
  exact flagged_projection oracle marked computation ((), flag)

/-- Any two fixed oracle realizations agreeing outside marked queries are close
up to the probability of making such a query. The adversary need not be deterministic. -/
theorem oracle_change_distance_le_hit (left right : Oracle) (marked : World.Domain → Bool)
    (agree : ∀ query, marked query = false → left.world query = right.world query)
    {α : Type} (computation : OracleComp World α) :
    measureTVDist (fixedOracleRun left computation) (fixedOracleRun right computation) ≤
      (prEvent ((fun result => result.2.2 = true) <$> (flaggedRun left marked computation))).toReal := by
  letI : MeasurableSpace (α × Unit × Bool) := ⊤
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

/-- Mark all compression inputs with a given low half. This conservatively includes
the single salted input being reprogrammed, whatever its message block is. -/
def marksSalt (salt : Digest) : World.Domain → Bool
  | .inr (.inl input) => decide (input.extractLsb' 0 256 = salt)
  | _ => false

/-- Update one compression cell; permutation and inverse remain exactly the same. -/
def programCompression (oracle : Oracle) (input : BitVec 512) (answer : Digest) : Oracle :=
  ⟨Function.update oracle.compression input answer, oracle.permutation⟩

theorem program_compression_agrees (oracle : Oracle) (input : BitVec 512) (answer : Digest)
    (query : World.Domain) (unmarked : marksSalt (input.extractLsb' 0 256) query = false) :
    oracle.world query = (programCompression oracle input answer).world query := by
  rcases query with coins | publicQuery
  · rfl
  · rcases publicQuery with requested | permQuery
    · have different : requested ≠ input := by
        intro same
        subst requested
        simp [marksSalt] at unmarked
        exact unmarked rfl
      simp only [Oracle.world, Oracle.answer, programCompression, QueryImpl.add_apply_inr,
        pure_inj]
      exact (Function.update_of_ne different answer oracle.compression).symm
    · rcases permQuery with forward | inverse <;> rfl

/-- Concrete reprogramming loss, charged against the original unprogrammed run.
In that run a separately sampled hidden salt cannot influence the adaptive queries. -/
theorem reprogram_compression_distance (oracle : Oracle) (input : BitVec 512) (answer : Digest)
    {α : Type} (computation : OracleComp World α) :
    measureTVDist (fixedOracleRun oracle computation)
      (fixedOracleRun (programCompression oracle input answer) computation) ≤
      (prEvent ((fun result => result.2.2 = true) <$> (flaggedRun oracle (marksSalt (input.extractLsb' 0 256)) computation))).toReal :=
  oracle_change_distance_le_hit oracle (programCompression oracle input answer) _
    (program_compression_agrees oracle input answer) computation

end CommitGolfCandidate
