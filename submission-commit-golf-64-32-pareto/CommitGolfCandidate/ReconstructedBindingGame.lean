import CommitGolfCandidate.ReconstructedBindingPaths
import CommitGolfCandidate.TwoPermutationCheckerReplay

namespace CommitGolfCandidate.Reconstruction.Binding
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker hiding checkerReplay checker_replay_bounded checker_replay_extracts
set_option maxRecDepth 8192
set_option exponentiation.threshold 2050

/-- The machine-side interface for the reconstructed checker. Each successful claim
must expose its pinned leaf and its authenticated route through the tagged tree. -/
def AcceptedPaths (s : Submission) : Prop :=
  ∀ (oracle : Oracle) (input : CheckInput),
    let observed := checkObservation s oracle input
    observed.1.1.exit = .success →
      observed.2 ≤ 2^31 ∧
      ∀ index : {i // i ∈ input.positions},
        Nonempty (Opening oracle index.val (input.values index) input.commitment observed.1.2)

def checkerReplay (s : Submission) (claim : Scheme.Claim) : OracleComp World Unit := do
  let _ ← limitPublicQueries (s.run .check (leftCheck claim)) (2^31)
  let _ ← limitPublicQueries (s.run .check (rightCheck claim)) (2^31)
  pure ()

theorem checker_replay_bounded (s : Submission) (claim : Scheme.Claim) :
    PublicQueryBound (checkerReplay s claim) (2^32) := by
  unfold checkerReplay
  change PublicQueryBound (_ >>= _) (2^31 + 2^31)
  apply public_query_bound_bind (limit_public_bound _ _)
  intro _
  change PublicQueryBound (_ >>= _) (2^31 + 0)
  apply public_query_bound_bind (limit_public_bound _ _)
  intro _
  trivial

private theorem one_limited_check (s : Submission) (oracle : Oracle) (input : CheckInput)
    (fits : (checkObservation s oracle input).2 ≤ 2^31) :
    fixedOracleRun oracle (recordRows (limitPublicQueries (s.run .check input) (2^31))) =
      pure (some (checkObservation s oracle input).1.1, (checkObservation s oracle input).1.2) := by
  have coinFree := check_public_only s input
  rw [(coinFree.limit (2^31)).record.fixed oracle, coinFree.limit_recorded oracle _ fits]
  rfl

theorem checker_replay_extracts (s : Submission) (refines : AcceptedPaths s)
    (oracle : Oracle) (claim : Scheme.Claim) (breaks : s.scheme.Breaks oracle claim) :
    ∀ result ∈ support (fixedOracleRun oracle (recordRows (checkerReplay s claim))), ReplayWitness result.2 := by
  obtain ⟨⟨index, member₀, member₁, conflict⟩, accepted₀, accepted₁⟩ := breaks
  let x := leftCheck claim
  let y := rightCheck claim
  have good₀ := checked_acceptance s oracle x accepted₀
  have good₁ := checked_acceptance s oracle y accepted₁
  obtain ⟨fits₀, path₀⟩ := refines oracle x good₀
  obtain ⟨fits₁, path₁⟩ := refines oracle y good₁
  have replay : fixedOracleRun oracle (recordRows (checkerReplay s claim)) =
      pure ((), (checkObservation s oracle x).1.2 ++ (checkObservation s oracle y).1.2) := by
    unfold checkerReplay
    change fixedOracleRun oracle
      (recordRows (do
        let _ ← limitPublicQueries (s.run .check x) (2^31)
        let _ ← limitPublicQueries (s.run .check y) (2^31)
        pure ())) = _
    have tail : fixedOracleRun oracle
        (recordRows (do let _ ← limitPublicQueries (s.run .check y) (2^31); pure ())) =
        pure ((), (checkObservation s oracle y).1.2) := by
      rw [record_rows_bind, fixed_oracle_run_bind, one_limited_check s oracle y fits₁]
      simp [record_rows_pure, fixed_oracle_run_pure, fixed_oracle_run_bind]
    rw [record_rows_bind, fixed_oracle_run_bind, one_limited_check s oracle x fits₀]
    simp only [pure_bind]
    rw [fixed_oracle_run_bind, tail]
    simp [fixed_oracle_run_pure]
  rw [replay]
  intro result found
  simp only [support_pure, Set.mem_singleton_iff] at found
  subst result
  exact opening_conflict oracle index claim.root _ _ conflict _ _
    (path₀ ⟨index, member₀⟩).some (path₁ ⟨index, member₁⟩).some

private theorem replay_dominated (s : Submission) (paths : AcceptedPaths s)
    (oracle : Oracle) (adversary : Scheme.Adversary) (budget : Nat) :
    Pr{let result ← oracle.run adversary}[s.scheme.Breaks oracle result.1 ∧ result.2 ≤ budget] ≤
      Pr{let result ← fixedOracleRun oracle (recordRows (boundedReplay (checkerReplay s) adversary budget))}[
        ReplayWitness result.2] := by
  classical
  let limited := limitPublicQueries adversary budget
  let start := fixedOracleRun oracle (recordRows limited)
  let good (limited : Option Scheme.Claim) := ∃ claim, limited = some claim ∧ s.scheme.Breaks oracle claim
  have projected : Prod.fst <$> start = fixedOracleRun oracle limited := by
    rw [← fixed_oracle_run_map, record_rows_erase]
  have prefixWin :
      Pr{let result ← start}[good result.1] =
        Pr{let result ← oracle.run adversary}[s.scheme.Breaks oracle result.1 ∧ result.2 ≤ budget] := by
    rw [← limit_public_probability oracle adversary budget (s.scheme.Breaks oracle)]
    have event := congrArg (fun x : ProbComp (Option Scheme.Claim) => Pr{let result ← x}[good result]) projected
    simpa only [prEvent_map, fixedOracleRun, Function.comp_def, good, limited] using event
  rw [← prefixWin]
  unfold boundedReplay
  rw [record_rows_bind, fixed_oracle_run_bind]
  change Pr{let result ← start}[good result.1] ≤ _
  rw [OracleComp.prEvent_bind_eq_tsum, OracleComp.prEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  rintro ⟨outcome, trace⟩
  by_cases winning : good outcome
  · obtain ⟨claim, fixed, breaks⟩ := winning
    subst outcome
    have sure :
      Pr{let result ← fixedOracleRun oracle (recordRows (replayOption (checkerReplay s) (some claim)) >>= fun next =>
        pure (next.1, trace ++ next.2))}[ReplayWitness result.2] = 1 := by
      rw [fixed_oracle_run_bind]
      apply prEvent_eq_one_of_forall_mem_support
      intro result reached
      obtain ⟨next, called, same⟩ := (mem_support_bind_iff _ _ _).mp reached
      rw [fixed_oracle_run_pure] at same
      simp only [support_pure, Set.mem_singleton_iff] at same
      subst result
      exact ReplayWitness.mono (fun _ present => List.mem_append_right trace present) (checker_replay_extracts s paths oracle claim breaks next called)
    have win : good (some claim) := ⟨claim, rfl, breaks⟩
    simp only [win, ite_true, sure, mul_one, start, limited]
    exact le_rfl
  · simp [winning]


theorem binding_of_accepted_paths (s : Submission) (paths : AcceptedPaths s) : s.scheme.Binding := by
  intro adversary budget positive
  let detected := boundedReplay (checkerReplay s) adversary budget
  have bounded : PublicQueryBound (recordRows detected) (budget + 2^32) := by
    apply record_rows_bound
    apply public_query_bound_bind (limit_public_bound adversary budget)
    intro limited
    cases limited with
    | none => trivial
    | some claim => exact checker_replay_bounded s claim
  have reduced :
      Pr{let (oracle,claim,calls) ← Scheme.bindingGame adversary}[s.scheme.Breaks oracle claim ∧ calls ≤ budget] ≤
      Pr{let r ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows detected))}[ReplayWitness r.2] := by
    simp only [Scheme.bindingGame,bind_pure_comp]
    rw [prEvent_bind_eq_tsum,prEvent_bind_eq_tsum]
    apply ENNReal.tsum_le_tsum
    intro oracle
    apply mul_le_mul_of_nonneg_left _ zero_le
    simp only [prEvent_map]
    exact replay_dominated s paths oracle adversary budget
  exact reduced.trans (joint_replay_bound detected budget (budget+2^32) positive le_rfl bounded)

end CommitGolfCandidate.Reconstruction.Binding
