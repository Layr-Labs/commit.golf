import CommitGolfCandidate.OverlapCommitTranscript
import CommitGolfCandidate.TwoPermutationOpeningResources
import CommitGolfCandidate.TwoPermutationOpeningTranscript
import CommitGolfCandidate.TwoPermutationCheckerReplay
import CommitGolfCandidate.TwoPermutationHonestBytes
import CommitGolfCandidate.Machine
import CommitGolfCandidate.CountingCoins

/-! Certificate assembly shared by layouts with the same checker and opener. -/
namespace TwoPermutationPrototype.WideCertificate
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

local instance {α : Type} : MeasurableSpace α := ⊤

variable {submission : Submission} {commitCycles : Nat}
variable (commitResources : ∀ (message : Message) (result : Execution),
  result ∈ support (submission.run .commit message) →
  result.exit = .success ∧ result.cycles = commitCycles ∧ result.oracleCalls = 50331647)
variable (openingABI : Opening.OpeningABI submission)
structure CheckerFacts (s : Submission) : Prop where
  terminates : ∀ (oracle : Oracle) (input : CheckInput),
    (Checker.checkObservation s oracle input).1.1.exit ≠ .unfinished
  queryBudget : ∀ (oracle : Oracle) (input : CheckInput),
    (Checker.checkObservation s oracle input).2 ≤ 26*input.positions.card
  acceptedTrace : Overlap.AcceptedTraceRefines s
  honestAccepted : ∀ (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape),
    (Checker.checkObservation s oracle
      (Checker.honestCheckInput oracle message positions salts)).1.1.exit = .success

theorem checker_facts_of_run {original : Submission}
    (same : ∀ input : CheckInput, submission.run .check input = original.run .check input)
    (checks : CheckerFacts original) : CheckerFacts submission := by
  have obs : ∀ oracle input, Checker.checkObservation submission oracle input =
      Checker.checkObservation original oracle input := by
    intro oracle input
    unfold Checker.checkObservation
    erw [same input]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro oracle input
    rw [obs]
    exact checks.terminates oracle input
  · intro oracle input
    rw [obs]
    exact checks.queryBudget oracle input
  · intro oracle input
    simp only [obs]
    exact checks.acceptedTrace oracle input
  · intro oracle message positions salts
    rw [obs]
    exact checks.honestAccepted oracle message positions salts

theorem checker_scheme_observation (oracle : Oracle) (input : CheckInput) :
    oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof) =
      let observed := Checker.checkObservation submission oracle input
      (observed.1.1.exit == .success, observed.2) := by
  rw [CommitGolfCandidate.scheme_check_evaluation]
  have erase := Checker.check_record_erase oracle (submission.run .check input)
  rw [← erase]
  rfl

private theorem checker_counted_observation (oracle : Oracle) (input : CheckInput) :
    oracle.run (submission.run .check input) =
      let observed := Checker.checkObservation submission oracle input
      pure (observed.1.1, observed.2) := by
  have erase := Checker.check_record_erase oracle (submission.run .check input)
  dsimp only [Checker.checkObservation] at ⊢
  erw [erase]
  by_cases valid : input.proof.length ≤ submission.sizes.proof
  · have run : submission.run .check input =
        execute (submission.image .check) (submission.steps .check)
          (submission.initialState .check input) false := by
      simp only [Submission.run, valid, decide_true, ite_true]
      rfl
    erw [run, CommitGolfCandidate.execute_check_evaluation]
  · have run : submission.run .check input = pure ⟨.failure,initialMachine,0,0⟩ := by
      simp only [Submission.run, valid, decide_false, Bool.false_eq_true, ite_false]
    erw [run, CommitGolfCandidate.oracle_run_pure, CommitGolfCandidate.check_evaluation_pure]

private theorem counted_commit_run (s : Submission) (oracle : Oracle) (message : Message)
    (execution : Execution × Nat)
    (reached : execution ∈ support (oracle.run (s.run .commit message))) :
    execution.1.oracleCalls = execution.2 :=
  CommitGolfCandidate.execute_counted_with_coins oracle (s.image .commit) (s.steps .commit)
    (s.initialState .commit message) true execution reached

private theorem mapped_commit_counter (s : Submission) (oracle : Oracle) (message : Message)
    (result : (Commitment × s.scheme.Trapdoor) × Nat)
    (reached : result ∈ support (oracle.run (s.scheme.commit message))) :
    ∃ execution : Execution × Nat,
      execution ∈ support (oracle.run (s.run .commit message)) ∧ execution.2 = result.2 := by
  let run : OracleComp World Execution := s.run .commit message
  change result ∈ support (oracle.run (s.readCommit <$> run)) at reached
  rw [CommitGolfCandidate.oracle_run_map oracle s.readCommit run,support_map] at reached
  obtain ⟨execution,reachable,same⟩ := reached
  exact ⟨execution,reachable,congrArg Prod.snd same⟩

include commitResources in
private theorem scheme_commit_budget (oracle : Oracle) (message : Message)
    (result : (Commitment × submission.scheme.Trapdoor) × Nat)
    (reached : result ∈ support (oracle.run (submission.scheme.commit message))) :
    result.2 ≤ COMMIT_BUDGET := by
  obtain ⟨executed,reachable,count⟩ := mapped_commit_counter submission oracle message result reached
  have actual := commitResources message executed.1
    (CommitGolfCandidate.writer_support (oracle.world.withAddCost Oracle.callCost) _ executed reachable)
  rw [←count,←counted_commit_run submission oracle message executed reachable,actual.2.2]
  decide

include openingABI in
private theorem supported_opening (trapdoor : submission.scheme.Trapdoor) (positions : Positions)
    (opened : Execution) (reached : opened ∈ support (submission.run .opening (trapdoor,positions))) :
    Opening.OpenPhysical submission trapdoor positions opened := by
  obtain ⟨answer,execution,physical⟩ := Opening.opening_physical submission openingABI trapdoor positions
  rw [execution,support_pure,Set.mem_singleton_iff] at reached
  rwa [reached]

include openingABI in
private theorem opening_success (trapdoor : submission.scheme.Trapdoor) (positions : Positions)
    (opened : Execution) (physical : Opening.OpenPhysical submission trapdoor positions opened) :
    submission.openingSucceeded opened = true := by
  have fit : (opened.state.getReg .x11).toNat ≤ submission.sizes.proof := by
    rw [physical.length]
    exact (Opening.opening_length_bound positions).trans openingABI.capacity
  simp only [Submission.openingSucceeded,physical.success,beq_self_eq_true,fit,decide_true,Bool.and_true]

include commitResources openingABI in
private theorem honest_machine_resources (message : Message) (positions : Positions)
    (result : MachineResult) (reached : result ∈ support (submission.honestMachine message positions)) :
    result.success = true ∧
      (positions.card = BATCH → result.commitCycles ≤ commitCycles ∧ result.openingCycles ≤ 42744) := by
  change result ∈ support (do
    let committed ← submission.run .commit message
    let opened ← submission.run .opening ((submission.readCommit committed).2,positions)
    pure ⟨committed.exit == Exit.success && submission.openingSucceeded opened,
      committed.cycles,opened.cycles,(submission.readProof opened).length⟩) at reached
  simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨committed,commitReached,opened,openReached,rfl⟩ := reached
  have commit := commitResources message committed commitReached
  have physical := supported_opening openingABI (submission.readCommit committed).2 positions opened openReached
  have openedCorrect := opening_success openingABI _ _ _ physical
  constructor
  · simp only [commit.1,beq_self_eq_true,openedCorrect,Bool.and_true]
  · intro batch
    exact ⟨commit.2.1.le,(Opening.opening_scored_limits submission _ positions opened physical batch).1⟩

include commitResources openingABI in
theorem submission_machine_success : submission.MachineSuccess := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (honest_machine_resources commitResources openingABI message positions result.1
    (CommitGolfCandidate.writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)).1

include commitResources openingABI in
theorem submission_prover_cycles : submission.ProverCycles commitCycles 42744 := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (honest_machine_resources commitResources openingABI message positions result.1
    (CommitGolfCandidate.writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)).2 batch

include commitResources openingABI in
theorem submission_termination (checks : CheckerFacts submission) : submission.Termination := by
  intro oracle program input
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  have execution := CommitGolfCandidate.writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached
  cases program with
  | commit =>
    rw [(commitResources input result.1 execution).1]
    decide
  | opening =>
    rw [(supported_opening openingABI input.1 input.2 result.1 execution).success]
    decide
  | check =>
    erw [checker_counted_observation oracle input] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact checks.terminates oracle input

include commitResources openingABI in
theorem submission_budgets (checks : CheckerFacts submission) : submission.scheme.HonestBudgets := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest,mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root,trapdoor⟩,calls⟩,committed,opened,opening,remainder⟩ := reached
  erw [Opening.scheme_open_bytes submission openingABI trapdoor positions,
    CommitGolfCandidate.oracle_run_pure] at opening
  simp only [support_pure,Set.mem_singleton_iff] at opening remainder
  subst opened
  subst result
  let input : CheckInput :=
    ⟨root,positions,message.restrict positions,Opening.proofFromTrapdoor (s := submission) trapdoor positions⟩
  have checked : (oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).2 ≤
      26*positions.card := by
    rw [checker_scheme_observation]
    exact checks.queryBudget oracle input
  exact ⟨scheme_commit_budget commitResources oracle message _ committed,Nat.zero_le _,checked.trans (by
    change 26*positions.card ≤ 100*positions.card
    omega)⟩

include openingABI in
private theorem opening_scheme_bytes_bound (trapdoor : submission.scheme.Trapdoor)
    (positions : Positions) (batch : positions.card = BATCH) :
    (Opening.proofFromTrapdoor (s := submission) trapdoor positions).length ≤ 71680 := by
  obtain ⟨opened,_,physical⟩ := Opening.opening_physical submission openingABI trapdoor positions
  rw [← Opening.read_opening_proof submission openingABI trapdoor positions opened physical]
  have length : (submission.readProof opened).length = (opened.state.getReg .x11).toNat := by
    simp only [Submission.readProof,opening_success openingABI _ _ _ physical,ite_true,
      List.length_map,List.length_range]
  rw [length]
  exact (Opening.opening_scored_limits submission _ positions opened physical batch).2

include openingABI in
theorem submission_proof_size : submission.scheme.ProofSize 71680 := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest,mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root,trapdoor⟩,calls⟩,_,opened,opening,remainder⟩ := reached
  erw [Opening.scheme_open_bytes submission openingABI trapdoor positions,
    CommitGolfCandidate.oracle_run_pure] at opening
  simp only [support_pure,Set.mem_singleton_iff] at opening remainder
  subst opened
  subst result
  exact opening_scheme_bytes_bound openingABI trapdoor positions batch

private theorem honest_check_event (s : Scheme) (oracle : Oracle)
    (message : Message) (positions : Positions) :
    (fun result : Scheme.HonestResult => result.accepted = true) <$> s.honest oracle message positions =
      (fun view : Commitment × Proof =>
        (oracle.eval (s.check view.1 positions (message.restrict positions) view.2)).1 = true) <$>
        CommitGolfCandidate.fixedOracleRun oracle (executableTranscript s message positions) := by
  simp only [Scheme.honest,executableTranscript,CommitGolfCandidate.fixed_oracle_run_bind,
    CommitGolfCandidate.fixed_oracle_run_pure,map_bind,map_pure]
  simp only [CommitGolfCandidate.fixedOracleRun,bind_map_left]

include openingABI in
set_option linter.constructorNameAsVariable false in
theorem submission_completeness (committed : Opening.PlbCommitTranscript submission) (checks : CheckerFacts submission) :
    submission.scheme.Completeness := by
  intro oracle message positions
  rw [honest_check_event]
  have refines := Opening.plb_transcript_refines submission openingABI committed oracle message positions
  rw [refines.prEvent_eq]
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro view reached
  simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨salts,_,rfl⟩ := reached
  let input := Checker.honestCheckInput oracle message positions salts
  change (oracle.eval (submission.scheme.check input.commitment input.positions input.values input.proof)).1 = true
  rw [checker_scheme_observation]
  dsimp only
  erw [checks.honestAccepted oracle message positions salts]
  rfl

include commitResources openingABI in
set_option linter.constructorNameAsVariable false in
theorem certificate_of_refinements (admitted : submission.Admission)
    (committed : Opening.PlbCommitTranscript submission)
    (checks : CheckerFacts submission) :
    Certificate submission 71680 commitCycles 42744 where
  admission := admitted
  machineSuccess := submission_machine_success commitResources openingABI
  termination := submission_termination commitResources openingABI checks
  completeness := submission_completeness openingABI committed checks
  honestBudgets := submission_budgets commitResources openingABI checks
  proofSize := submission_proof_size openingABI
  proverCycles := submission_prover_cycles commitResources openingABI
  binding := Checker.overlap_binding submission checks.acceptedTrace
  hidingProperty := Opening.plb_scheme_hiding submission openingABI committed

end TwoPermutationPrototype.WideCertificate
