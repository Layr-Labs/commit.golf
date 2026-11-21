import CommitGolfCandidate.ChainedOpeningPaths
import CommitGolfCandidate.ChainedRecordedProbability
import CommitGolfCandidate.TwoPermutationCheckerReplay

/-! Accepted machine checks give the recorded evidence used by chained binding. -/
namespace CommitGolfCandidate.Chained.Checker
open CommitGolf CommitGolf.Riscv OracleComp
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (leftCheck rightCheck checkObservation checked_acceptance)
set_option maxRecDepth 8192
set_option exponentiation.threshold 2100

def AcceptedTraceRefines (enc : Encoding) (s : Submission) : Prop :=
  ∀ (oracle : Oracle) (input : CheckInput),
    let observed := checkObservation s oracle input
    observed.1.1.exit = .success →
      observed.2 ≤ 2^31 ∧
      ∀ index : {i // i ∈ input.positions},
        Nonempty (RecordedOpening enc calls width oracle index.val (input.values index)
          (input.commitment.extractLsb' 0 238) observed.1.2)

def checkerReplay (s : Submission) (claim : Scheme.Claim) : OracleComp World Unit := do
  let _ ← limitPublicQueries (s.run .check (leftCheck claim)) (2^31)
  let _ ← limitPublicQueries (s.run .check (rightCheck claim)) (2^31)
  pure ()

theorem checker_replay_bounded (s : Submission) (claim : Scheme.Claim) :
    PublicQueryBound (checkerReplay s claim) (2^32) := by
  unfold checkerReplay
  change PublicQueryBound (_ >>= _) (2^31+2^31)
  apply public_query_bound_bind (limit_public_bound _ _)
  intro _
  change PublicQueryBound (_ >>= _) (2^31+0)
  apply public_query_bound_bind (limit_public_bound _ _)
  intro _
  trivial

private theorem one_limited_check (s : Submission) (oracle : Oracle) (input : CheckInput)
    (fits : (checkObservation s oracle input).2 ≤ 2^31) :
    fixedOracleRun oracle (recordRows (limitPublicQueries (s.run .check input) (2^31))) =
      pure (some (checkObservation s oracle input).1.1,(checkObservation s oracle input).1.2) := by
  have coinFree := TwoPermutationPrototype.Checker.check_public_only s input
  rw [(coinFree.limit (2^31)).record.fixed oracle,coinFree.limit_recorded oracle _ fits]
  rfl

theorem checker_replay_extracts (enc : Encoding) (s : Submission) (refines : AcceptedTraceRefines enc s)
    (oracle : Oracle) (claim : Scheme.Claim) (breaks : s.scheme.Breaks oracle claim) :
    ∀ result ∈ support (fixedOracleRun oracle (recordRows (checkerReplay s claim))),
      RecordedFailure enc calls width result.2 := by
  obtain ⟨⟨index,member₀,member₁,conflict⟩,accepted₀,accepted₁⟩ := breaks
  let x := leftCheck claim
  let y := rightCheck claim
  obtain ⟨fits₀,path₀⟩ := refines oracle x (checked_acceptance s oracle x accepted₀)
  obtain ⟨fits₁,path₁⟩ := refines oracle y (checked_acceptance s oracle y accepted₁)
  have replay : fixedOracleRun oracle (recordRows (checkerReplay s claim)) =
      pure ((),(checkObservation s oracle x).1.2++(checkObservation s oracle y).1.2) := by
    unfold checkerReplay
    change fixedOracleRun oracle
      (recordRows (do
        let _ ← limitPublicQueries (s.run .check x) (2^31)
        let _ ← limitPublicQueries (s.run .check y) (2^31)
        pure ())) = _
    have tail : fixedOracleRun oracle
        (recordRows (do let _ ← limitPublicQueries (s.run .check y) (2^31); pure ())) =
        pure ((),(checkObservation s oracle y).1.2) := by
      rw [record_rows_bind,fixed_oracle_run_bind,one_limited_check s oracle y fits₁]
      simp [record_rows_pure,fixed_oracle_run_pure,fixed_oracle_run_bind]
    rw [record_rows_bind,fixed_oracle_run_bind,one_limited_check s oracle x fits₀]
    simp only [pure_bind]
    rw [fixed_oracle_run_bind,tail]
    simp [fixed_oracle_run_pure]
  rw [replay]
  intro result found
  simp only [support_pure,Set.mem_singleton_iff] at found
  subst result
  exact recorded_openings_conflict width_upper oracle index (claim.root.extractLsb' 0 238)
    _ _ conflict _ _ (path₀ ⟨index,member₀⟩).some (path₁ ⟨index,member₁⟩).some

def bindingReplay (enc : Encoding) (s : Submission) (refines : AcceptedTraceRefines enc s) :
    BindingReplay s.scheme (RecordedFailure enc calls width) :=
  ⟨checkerReplay s,checker_replay_bounded s,checker_replay_extracts enc s refines⟩

theorem binding_of_accepted_trace (enc : Encoding) (s : Submission) (refines : AcceptedTraceRefines enc s) :
    s.scheme.Binding := scheme_binding_of_recorded_replay s.scheme enc (bindingReplay enc s refines)

end CommitGolfCandidate.Chained.Checker
