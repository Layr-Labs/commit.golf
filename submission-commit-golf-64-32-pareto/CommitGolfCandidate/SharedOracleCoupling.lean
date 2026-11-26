import CommitGolfCandidate.TwoPermutationHidingSequence
import CommitGolfCandidate.HidingReprogram

/-! Direct two-world coupling, charged to a single common reference run. -/
namespace CommitGolfCandidate.SharedOracle
open CommitGolf OracleComp OracleComp.ProgramLogic.Relational
local instance {α : Type} : MeasurableSpace α := ⊤

private theorem step_flag (oracle : Oracle) (marked : World.Domain → Bool)
    (query : World.Domain) (state : Unit × Bool) (result : World.Range query × Unit × Bool)
    (reached : result ∈ support ((flaggedHandler oracle marked query).run state)) :
    result.2.2 = (state.2 || marked query) := by
  rw [flagged_handler_run] at reached
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨answer, _, rfl⟩ := reached
  rfl

private theorem monotone (oracle : Oracle) (marked : World.Domain → Bool)
    (query : World.Domain) (state : Unit × Bool) (bad : state.2 = true)
    (result : World.Range query × Unit × Bool)
    (reached : result ∈ support ((flaggedHandler oracle marked query).run state)) :
    result.2.2 = true := by
  rw [step_flag oracle marked query state result reached, bad, Bool.true_or]

private theorem good_agree (left right : Oracle) (marked : World.Domain → Bool)
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
      have flag := step_flag oracle marked query state result reached
      exact bad.2 (by simpa [hit] using flag)
    rw [zero left, zero right]

theorem distance_le_reference_hit (reference left right : Oracle)
    (marked : World.Domain → Bool)
    (left_agree : ∀ query, marked query = false → reference.world query = left.world query)
    (right_agree : ∀ query, marked query = false → reference.world query = right.world query)
    {α : Type} (program : OracleComp World α) :
    measureTVDist (fixedOracleRun left program) (fixedOracleRun right program) ≤
      (Pr{let result ← flaggedRun reference marked program}[result.2.2 = true]).toReal := by
  have hit := prEvent_simulateQ_run_bad_eq
    (flaggedHandler reference marked) (flaggedHandler left marked) (fun state => state.2 = true)
    (good_agree reference left marked left_agree)
    (monotone reference marked) (monotone left marked) program ((), false)
  have bound := oracle_change_distance_le_hit left right marked
    (fun query safe => (left_agree query safe).symm.trans (right_agree query safe)) program
  change measureTVDist (fixedOracleRun left program) (fixedOracleRun right program) ≤
    (Pr{let result ← flaggedRun left marked program}[result.2.2 = true]).toReal at bound
  change Pr{let result ← flaggedRun reference marked program}[result.2.2 = true] =
    Pr{let result ← flaggedRun left marked program}[result.2.2 = true] at hit
  rwa [← hit] at bound

end CommitGolfCandidate.SharedOracle
