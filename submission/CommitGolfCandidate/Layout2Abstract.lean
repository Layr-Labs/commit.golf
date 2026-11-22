import CommitGolfCandidate.QuartetCounterCertificate

/-! Abstract re-encoded proof layer ("M2") for Layout 2.

Generalizes the linked-salt hiding refinement, checker facts, opening facts, completeness, and
certificate assembly to an arbitrary proof encoder `enc : Positions → Proof → Proof` (instantiated
in Layout 2 by the opener's `unconv` layout). Existing modules are left untouched; setting
`enc := fun _ proof => proof` recovers the original statements verbatim. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

/-! ### 1. Re-encoded Linked-Salt Refinement and Two-Stage Hiding -/

namespace TwoPermutationPrototype.Sampling.Quartet
open CommitGolf OracleComp CommitGolfCandidate
open CommitGolfCandidate.Permutation.NonceChain (Key)
local instance layout2AbstractDiscrete {α : Type} : MeasurableSpace α := ⊤

/-- The executable transcript is the honest Quartet linked-salt view with `enc p` applied to the
proof component. -/
def LinkedQuartetRefinesEnc (σ : Permutation.LinkedSalt.Schedule Permutation.CounterSalt.groups)
    (enc : Positions → Proof → Proof) (scheme : Scheme) : Prop :=
  ∀ (o : Oracle) (m : Message) (p : Positions), fixedOracleRun o (executableTranscript scheme m p) =ᵈ
    (do let k ← $ᵗ Key
        let view := honestView builder o.compression (BiPermutation.equiv Block o.permutation) m p
          (Permutation.LinkedSalt.salts σ o.permutation k)
        pure (view.1, enc p view.2))

/-- Pack `challenge.positions` into the auxiliary state so stage 2 can apply `enc positions`. -/
def liftChallenge {State : Type} {openingSize : Nat}
    (challenge : Hiding.HidingChallenge State openingSize) :
    Hiding.HidingChallenge (State × Positions) openingSize where
  message₀ := challenge.message₀
  message₁ := challenge.message₁
  positions := challenge.positions
  size_eq := challenge.size_eq
  agree := challenge.agree
  aux := (challenge.aux, challenge.positions)

/-- Post-processing adversary adapter: stage 1 remembers `challenge.positions` in its state, and
stage 2 applies `enc positions` to the received proof before invoking `adversary.observe`. -/
def encodeAdversary (enc : Positions → Proof → Proof)
    {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) :
    Hiding.HidingAdversary (State × Positions) Output openingSize where
  choose := liftChallenge <$> adversary.choose
  observe := fun state root proof => adversary.observe state.1 root (enc state.2 proof)

/-- Pure post-processing of the proof and state tagging introduces zero oracle queries. -/
theorem encode_adversary_query_bound (enc : Positions → Proof → Proof)
    {State Output : Type} {openingSize budget : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget) :
    Hiding.QueryBound (encodeAdversary enc adversary) budget := by
  intro first reached
  change first ∈ support (Hiding.counted (liftChallenge <$> adversary.choose)) at reached
  rw [Hiding.counted, costDist_map] at reached
  change first ∈ support ((fun result : Hiding.HidingChallenge State openingSize × Nat =>
    (liftChallenge result.1, result.2)) <$> Hiding.counted adversary.choose) at reached
  rw [support_map] at reached
  obtain ⟨orig, origReached, rfl⟩ := reached
  have hOrig := bounded orig origReached
  refine ⟨hOrig.1, ?_⟩
  intro root proof last lastReached
  exact hOrig.2 root (enc orig.1.positions proof) last lastReached

private theorem executable_to_linked_enc
    (σ : Permutation.LinkedSalt.Schedule Permutation.CounterSalt.groups)
    (enc : Positions → Proof → Proof)
    {State Output : Type} {openingSize : Nat}
    (scheme : Scheme) (refines : LinkedQuartetRefinesEnc σ enc scheme)
    (adversary : Hiding.HidingAdversary State Output openingSize) (which : Bool) :
    Hiding.runHiding (Hiding.hidingExperiment scheme adversary which) =ᵈ
      sampledLinked σ (encodeAdversary enc adversary) which := by
  have grouping :
      Hiding.hidingExperiment scheme adversary which = (do
        let challenge ← adversary.choose
        let message := if which then challenge.message₁ else challenge.message₀
        let (root, proof) ← executableTranscript scheme message challenge.positions
        adversary.observe challenge.aux root proof) := by
    simp [Hiding.hidingExperiment, executableTranscript, bind_assoc]
  have counted :
      Hiding.runHiding (Hiding.hidingExperiment scheme adversary which) =
        (Oracle.sample >>= fun oracle =>
          fixedOracleRun oracle (Hiding.hidingExperiment scheme adversary which)) := by
    simp only [Hiding.runHiding, fixedOracleRun, map_eq_bind_pure_comp, Function.comp_def]
  rw [counted]
  unfold sampledLinked
  apply EvalDistEq.bind_right Oracle.sample
  intro oracle
  rw [grouping, fixed_oracle_run_bind]
  change (fixedOracleRun oracle adversary.choose >>= _) =ᵈ
    (fixedOracleRun oracle (liftChallenge <$> adversary.choose) >>= _)
  rw [fixed_oracle_run_map, bind_map_left]
  apply EvalDistEq.bind_right
  intro challenge
  rw [fixed_oracle_run_bind]
  let message := if which then challenge.message₁ else challenge.message₀
  apply ((refines oracle message challenge.positions).bind_left
    (fun (view : Commitment × Proof) => fixedOracleRun oracle
      (adversary.observe challenge.aux view.1 view.2))).trans
  simp only [bind_assoc, pure_bind, observeTranscriptView, encodeAdversary, liftChallenge, message]
  apply EvalDistEq.bind_right
  intro k
  have equivalentOracle :
      fixedOracle oracle.compression (BiPermutation.equiv Block oracle.permutation) = oracle := by
    unfold fixedOracle
    rw [Equiv.symm_apply_apply]
  rw [equivalentOracle]

/-- Any re-encoded linked-salt refinement gives the challenge's two-stage hiding clause, with no
injectivity or length requirement on `enc`. -/
theorem scheme_hiding_of_linked_enc
    (σ : Permutation.LinkedSalt.Schedule Permutation.CounterSalt.groups)
    (enc : Positions → Proof → Proof) (scheme : Scheme)
    (refines : LinkedQuartetRefinesEnc σ enc scheme) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  constructor
  · intro _ budget
    positivity
  · intro openingSize budget _ State Output adversary bounded
    unfold measureTVDist
    rw [(executable_to_linked_enc σ enc scheme refines adversary false).evalDist_eq,
      (executable_to_linked_enc σ enc scheme refines adversary true).evalDist_eq]
    exact linked_reference_hiding σ (encodeAdversary enc adversary)
      (encode_adversary_query_bound enc adversary bounded)

/-- Sanity equivalence: with `enc := fun _ proof => proof`, `LinkedQuartetRefinesEnc` is
`LinkedQuartetRefines`. -/
theorem linked_quartet_refines_enc_id
    (σ : Permutation.LinkedSalt.Schedule Permutation.CounterSalt.groups) (scheme : Scheme) :
    LinkedQuartetRefinesEnc σ (fun _ proof => proof) scheme ↔ LinkedQuartetRefines σ scheme := by
  rfl

/-- Sanity instance: recovering `scheme_hiding_of_linked` from `scheme_hiding_of_linked_enc`. -/
theorem scheme_hiding_of_linked_from_enc
    (σ : Permutation.LinkedSalt.Schedule Permutation.CounterSalt.groups)
    (scheme : Scheme) (refines : LinkedQuartetRefines σ scheme) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) :=
  scheme_hiding_of_linked_enc σ (fun _ proof => proof) scheme
    ((linked_quartet_refines_enc_id σ scheme).mpr refines)

end TwoPermutationPrototype.Sampling.Quartet

/-! ### 2. Generalized Checker Facts (Encoder-Side and M1 Decoder-Side Bridge) -/

namespace TwoPermutationPrototype.QuartetCertificate
open CommitGolf CommitGolf.Riscv CommitGolfCandidate OracleComp TwoPermutationPrototype.Sampling

/-- The honest checker input with `enc positions` applied to the canonical honest proof; the
commitment, positions, and values are unchanged. -/
def honestCheckInputEnc (enc : Positions → Proof → Proof)
    (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) : CheckInput :=
  let base := honestCheckInput oracle message positions salts
  { base with proof := enc positions base.proof }

/-- Checker facts parameterized by an honest-proof encoder `enc`. Termination, query budget, and
binding are unchanged from `CheckerFacts`. -/
structure CheckerFactsEnc (enc : Positions → Proof → Proof) (s : Submission) : Prop where
  terminates : ∀ oracle input, (Checker.checkObservation s oracle input).1.1.exit ≠ .unfinished
  queryBudget : ∀ oracle input, (Checker.checkObservation s oracle input).2 ≤ 100 * input.positions.card
  binding : s.scheme.Binding
  honestAccepted : ∀ oracle message positions salts,
    (Checker.checkObservation s oracle
      (honestCheckInputEnc enc oracle message positions salts)).1.1.exit = .success

/-- M1 decoder-side checker facts: the delivered checker terminates, respects the query budget, is
binding (all independent of `enc` and `dec`), and accepts any admitted external input `input` whose
converted proof `dec input.positions input.proof` reproduces the canonical honest input. -/
structure CheckerFactsDec (dec : Positions → Proof → Proof) (s : Submission) : Prop where
  terminates : ∀ oracle input, (Checker.checkObservation s oracle input).1.1.exit ≠ .unfinished
  queryBudget : ∀ oracle input, (Checker.checkObservation s oracle input).2 ≤ 100 * input.positions.card
  binding : s.scheme.Binding
  convertedAccepted : ∀ oracle message positions salts (input : CheckInput),
    input.proof.length ≤ s.sizes.proof →
    { input with proof := dec input.positions input.proof } =
      honestCheckInput oracle message positions salts →
    (Checker.checkObservation s oracle input).1.1.exit = .success

/-- Plug M1 (`CheckerFactsDec dec s`) into `CheckerFactsEnc enc s` using round-trip on honest
proofs and proof-buffer admission of the encoded honest proof. -/
theorem checker_facts_enc_of_dec (dec enc : Positions → Proof → Proof) (s : Submission)
    (checks : CheckerFactsDec dec s)
    (roundTrip : ∀ oracle message positions salts,
      dec positions (enc positions (honestCheckInput oracle message positions salts).proof) =
        (honestCheckInput oracle message positions salts).proof)
    (encFits : ∀ oracle message positions salts,
      (enc positions (honestCheckInput oracle message positions salts).proof).length ≤ s.sizes.proof) :
    CheckerFactsEnc enc s where
  terminates := checks.terminates
  queryBudget := checks.queryBudget
  binding := checks.binding
  honestAccepted := fun oracle message positions salts => by
    apply checks.convertedAccepted oracle message positions salts
      (honestCheckInputEnc enc oracle message positions salts)
    · exact encFits oracle message positions salts
    · change { honestCheckInput oracle message positions salts with
        proof := dec positions (enc positions (honestCheckInput oracle message positions salts).proof) } =
        honestCheckInput oracle message positions salts
      rw [roundTrip oracle message positions salts]

/-- Handle the oversized-proof branch (`s.sizes.proof < input.proof.length`) uniformly for any
submission `s`: `Submission.run` rejects oversized proofs before loading, with 0 oracle calls. -/
theorem checker_facts_dec_of_admitted (dec : Positions → Proof → Proof) (s : Submission)
    (terminatesAdmitted : ∀ oracle (input : CheckInput), input.proof.length ≤ s.sizes.proof →
      (Checker.checkObservation s oracle input).1.1.exit ≠ .unfinished)
    (queryBudgetAdmitted : ∀ oracle (input : CheckInput), input.proof.length ≤ s.sizes.proof →
      (Checker.checkObservation s oracle input).2 ≤ 100 * input.positions.card)
    (binding : s.scheme.Binding)
    (convertedAccepted : ∀ oracle message positions salts (input : CheckInput),
      input.proof.length ≤ s.sizes.proof →
      { input with proof := dec input.positions input.proof } =
        honestCheckInput oracle message positions salts →
      (Checker.checkObservation s oracle input).1.1.exit = .success) :
    CheckerFactsDec dec s where
  terminates := fun oracle input => by
    by_cases h : input.proof.length ≤ s.sizes.proof
    · exact terminatesAdmitted oracle input h
    · have run : s.run .check input = pure ⟨.failure, Riscv.initialMachine, 0, 0⟩ := by
        simp only [Submission.run, h, decide_false, Bool.false_eq_true, ite_false]
      unfold Checker.checkObservation
      rw [run, record_rows_pure, check_evaluation_pure]
      decide
  queryBudget := fun oracle input => by
    by_cases h : input.proof.length ≤ s.sizes.proof
    · exact queryBudgetAdmitted oracle input h
    · have run : s.run .check input = pure ⟨.failure, Riscv.initialMachine, 0, 0⟩ := by
        simp only [Submission.run, h, decide_false, Bool.false_eq_true, ite_false]
      unfold Checker.checkObservation
      rw [run, record_rows_pure, check_evaluation_pure]
      exact Nat.zero_le _
  binding := binding
  convertedAccepted := convertedAccepted

/-- Variant of `checker_facts_enc_of_dec` taking length preservation of `enc` on honest proofs
together with admission of the canonical honest proof. -/
theorem checker_facts_enc_of_dec_length (dec enc : Positions → Proof → Proof) (s : Submission)
    (checks : CheckerFactsDec dec s)
    (roundTrip : ∀ oracle message positions salts,
      dec positions (enc positions (honestCheckInput oracle message positions salts).proof) =
        (honestCheckInput oracle message positions salts).proof)
    (encLength : ∀ oracle message positions salts,
      (enc positions (honestCheckInput oracle message positions salts).proof).length =
        (honestCheckInput oracle message positions salts).proof.length)
    (honestFits : ∀ oracle message positions salts,
      (honestCheckInput oracle message positions salts).proof.length ≤ s.sizes.proof) :
    CheckerFactsEnc enc s :=
  checker_facts_enc_of_dec dec enc s checks roundTrip (fun oracle message positions salts => by
    rw [encLength oracle message positions salts]
    exact honestFits oracle message positions salts)

/-- Sanity equivalence: with `enc := fun _ proof => proof`, `honestCheckInputEnc` is
`honestCheckInput`. -/
@[simp] theorem honest_check_input_enc_id (oracle : Oracle) (message : Message)
    (positions : Positions) (salts : CompleteSaltTape) :
    honestCheckInputEnc (fun _ proof => proof) oracle message positions salts =
      honestCheckInput oracle message positions salts := by
  rfl

/-- Sanity equivalence: with `enc := fun _ proof => proof`, `CheckerFactsEnc` is `CheckerFacts`. -/
theorem checker_facts_enc_id (s : Submission) :
    CheckerFactsEnc (fun _ proof => proof) s ↔ CheckerFacts s := by
  constructor
  · intro h
    exact ⟨h.terminates, h.queryBudget, h.binding, h.honestAccepted⟩
  · intro h
    exact ⟨h.terminates, h.queryBudget, h.binding, h.honestAccepted⟩

end TwoPermutationPrototype.QuartetCertificate

/-! ### 3. Re-encoded Opening Facts, Completeness, and Certificate Assembly -/

namespace TwoPermutationPrototype.QuartetCounterCertificate
open CommitGolf CommitGolf.Riscv CommitGolfCandidate OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuartetCertificate
  (CheckerFacts CheckerFactsEnc CheckerFactsDec honestCheckInput honestCheckInputEnc
   checker_facts_enc_of_dec_length checker_facts_enc_id)
open CommitGolfCandidate.Permutation.NonceChain (Key)

local instance layout2CounterDiscrete {α : Type} : MeasurableSpace α := ⊤

/-- Opening facts parameterized by an honest-proof encoder `enc`. The resource clause `runs` is
identical to `OpeningFacts.runs`. -/
structure OpeningFactsEnc (enc : Positions → Proof → Proof) (s : Submission)
    (openingCycles proofBytes : Nat) : Prop where
  runs : ∀ (trapdoor : s.scheme.Trapdoor) (positions : Positions) (result : Execution),
    result ∈ support (s.run .opening (trapdoor, positions)) →
    result.exit = .success ∧ s.openingSucceeded result = true ∧
    (positions.card = BATCH → result.cycles ≤ openingCycles ∧ (s.readProof result).length ≤ proofBytes) ∧
    result.oracleCalls ≤ 100 * positions.card
  refines : Sampling.Quartet.LinkedQuartetRefinesEnc linkedSchedule enc s.scheme

/-- Assemble `LinkedQuartetRefinesEnc` from commit distribution, deterministic opening, root match,
and encoded proof match (`proofOf o (stash o m k) p = enc p honestProof`). -/
theorem linked_refines_of_parts_enc (scheme : Scheme)
    (enc : Positions → Proof → Proof)
    (root : Oracle → Message → Key → Commitment) (stash : Oracle → Message → Key → scheme.Trapdoor)
    (proofOf : Oracle → scheme.Trapdoor → Positions → Proof)
    (commits : ∀ o m, fixedOracleRun o (scheme.commit m) =ᵈ
      (do let k ← $ᵗ Key; pure (root o m k, stash o m k)))
    (opens : ∀ o td p, fixedOracleRun o (scheme.opening td p) = pure (proofOf o td p))
    (rootEq : ∀ o m k p, root o m k = (Sampling.Quartet.honestView Sampling.Quartet.builder o.compression
      (BiPermutation.equiv Block o.permutation) m p (Permutation.LinkedSalt.salts linkedSchedule o.permutation k)).1)
    (proofEq : ∀ o m k p, proofOf o (stash o m k) p = enc p (Sampling.Quartet.honestView Sampling.Quartet.builder
      o.compression (BiPermutation.equiv Block o.permutation) m p
      (Permutation.LinkedSalt.salts linkedSchedule o.permutation k)).2) :
    Sampling.Quartet.LinkedQuartetRefinesEnc linkedSchedule enc scheme := by
  intro o m p
  unfold executableTranscript
  rw [fixed_oracle_run_bind]
  apply ((commits o m).bind_left _).trans
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro k
  rw [fixed_oracle_run_bind, opens, pure_bind, fixed_oracle_run_pure, rootEq o m k p, proofEq o m k p]

variable {s : Submission} {enc : Positions → Proof → Proof}
variable {commitCycles openingCycles proofBytes : Nat}
variable (commit : ∀ (message : Message) (result : Execution), result ∈ support (s.run .commit message) →
  result.exit = .success ∧ result.cycles = commitCycles ∧ result.oracleCalls ≤ COMMIT_BUDGET)

private theorem scheme_check_observation_enc (oracle : Oracle) (input : CheckInput) :
    oracle.eval (s.scheme.check input.commitment input.positions input.values input.proof) =
      let observed := Checker.checkObservation s oracle input
      (observed.1.1.exit == .success, observed.2) := by
  rw [scheme_check_evaluation]
  have erase := Checker.check_record_erase oracle (s.run .check input)
  rw [← erase]
  rfl

private theorem counted_check_observation_enc (oracle : Oracle) (input : CheckInput) :
    oracle.run (s.run .check input) =
      let observed := Checker.checkObservation s oracle input
      pure (observed.1.1, observed.2) := by
  have erase := Checker.check_record_erase oracle (s.run .check input)
  dsimp only [Checker.checkObservation] at ⊢
  erw [erase]
  by_cases valid : input.proof.length ≤ s.sizes.proof
  · have run : s.run .check input = execute (s.image .check) (s.steps .check)
        (s.initialState .check input) false := by
      simp only [Submission.run, valid, decide_true, ite_true]
      rfl
    erw [run, execute_check_evaluation]
  · have run : s.run .check input = pure ⟨.failure, initialMachine, 0, 0⟩ := by
      simp only [Submission.run, valid, decide_false, Bool.false_eq_true, ite_false]
    erw [run, oracle_run_pure, check_evaluation_pure]

include commit in
private theorem scheme_commit_budget_enc (oracle : Oracle) (message : Message)
    (result : (Commitment × s.scheme.Trapdoor) × Nat)
    (reached : result ∈ support (oracle.run (s.scheme.commit message))) :
    result.2 ≤ COMMIT_BUDGET := by
  change result ∈ support (oracle.run (s.readCommit <$> s.run .commit message)) at reached
  rw [oracle_run_map oracle s.readCommit, support_map] at reached
  obtain ⟨execution, execReached, same⟩ := reached
  have actual := commit message execution.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ execution execReached)
  have calls := execute_counted_with_coins oracle (s.image .commit) (s.steps .commit)
    (s.initialState .commit message) true execution execReached
  have equal : execution.2 = result.2 := congrArg Prod.snd same
  rw [← equal, ← calls]
  exact actual.2.2

private theorem opening_run_enc (opens : OpeningFactsEnc enc s openingCycles proofBytes)
    (trapdoor : s.scheme.Trapdoor) (positions : Positions)
    (opened : Execution) (reached : opened ∈ support (s.run .opening (trapdoor, positions))) :
    opened.exit = .success ∧ s.openingSucceeded opened = true ∧
    (positions.card = BATCH → opened.cycles ≤ openingCycles ∧ (s.readProof opened).length ≤ proofBytes) := by
  have r := opens.runs trapdoor positions opened reached
  exact ⟨r.1, r.2.1, r.2.2.1⟩

include commit in
private theorem honest_machine_resources_enc (opens : OpeningFactsEnc enc s openingCycles proofBytes)
    (message : Message) (positions : Positions)
    (result : MachineResult) (reached : result ∈ support (s.honestMachine message positions)) :
    result.success = true ∧
      (positions.card = BATCH → result.commitCycles ≤ commitCycles ∧ result.openingCycles ≤ openingCycles) := by
  change result ∈ support (do
    let committed ← s.run .commit message
    let opened ← s.run .opening ((s.readCommit committed).2, positions)
    pure ⟨committed.exit == Exit.success && s.openingSucceeded opened,
      committed.cycles, opened.cycles, (s.readProof opened).length⟩) at reached
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨committed, commitReached, opened, openReached, rfl⟩ := reached
  have finished := commit message committed commitReached
  have physical := opening_run_enc opens (s.readCommit committed).2 positions opened openReached
  constructor
  · simp only [finished.1, beq_self_eq_true, physical.2.1, Bool.and_true]
  · intro batch
    exact ⟨finished.2.1.le, (physical.2.2 batch).1⟩

include commit in
theorem machine_success_enc (opens : OpeningFactsEnc enc s openingCycles proofBytes) :
    s.MachineSuccess := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (honest_machine_resources_enc commit opens message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)).1

include commit in
theorem prover_cycles_enc (opens : OpeningFactsEnc enc s openingCycles proofBytes) :
    s.ProverCycles commitCycles openingCycles := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (honest_machine_resources_enc commit opens message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)).2 batch

include commit in
theorem termination_enc (opens : OpeningFactsEnc enc s openingCycles proofBytes)
    (checks : CheckerFactsEnc enc s) : s.Termination := by
  intro oracle program input
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  have execution := writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached
  cases program with
  | commit =>
    rw [(commit input result.1 execution).1]
    decide
  | opening =>
    rw [(opening_run_enc opens input.1 input.2 result.1 execution).1]
    decide
  | check =>
    erw [counted_check_observation_enc oracle input] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact checks.terminates oracle input

private theorem opening_sample_enc (opens : OpeningFactsEnc enc s openingCycles proofBytes)
    (oracle : Oracle) (trapdoor : s.scheme.Trapdoor) (p : Positions) (sample : Proof × Nat)
    (reached : sample ∈ support (oracle.run (s.scheme.opening trapdoor p))) :
    sample.2 ≤ 100 * p.card ∧ (p.card = BATCH → sample.1.length ≤ proofBytes) := by
  change sample ∈ support (oracle.run (s.readProof <$> s.run .opening (trapdoor, p))) at reached
  rw [oracle_run_map, support_map] at reached
  obtain ⟨ex, hit, rfl⟩ := reached
  have raw := writer_support (oracle.world.withAddCost Oracle.callCost) _ ex hit
  have info := opens.runs trapdoor p ex.1 raw
  have counted := execute_counted_with_coins oracle (s.image .opening) (s.steps .opening)
    (s.initialState .opening (trapdoor, p)) true ex hit
  exact ⟨(by rw [← counted]; exact info.2.2.2), fun b => (info.2.2.1 b).2⟩

include commit in
theorem honest_budgets_enc (opens : OpeningFactsEnc enc s openingCycles proofBytes)
    (checks : CheckerFactsEnc enc s) : s.scheme.HonestBudgets := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest, mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root, trapdoor⟩, calls⟩, committed, opened, opening, remainder⟩ := reached
  have sample := opening_sample_enc opens oracle trapdoor positions opened opening
  simp only [support_pure, Set.mem_singleton_iff] at remainder
  subst result
  let input : CheckInput := ⟨root, positions, message.restrict positions, opened.1⟩
  have checked : (oracle.eval (s.scheme.check input.commitment input.positions input.values input.proof)).2 ≤
      100 * positions.card := by
    rw [scheme_check_observation_enc]
    exact checks.queryBudget oracle input
  exact ⟨scheme_commit_budget_enc commit oracle message _ committed, sample.1, checked⟩

theorem proof_size_enc (opens : OpeningFactsEnc enc s openingCycles proofBytes) :
    s.scheme.ProofSize proofBytes := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest, mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root, trapdoor⟩, calls⟩, _, opened, opening, remainder⟩ := reached
  have sample := opening_sample_enc opens oracle trapdoor positions opened opening
  simp only [support_pure, Set.mem_singleton_iff] at remainder
  subst result
  exact sample.2 batch

/-- Alternative `ProofSize` proof directly from `LinkedQuartetRefinesEnc` and a length bound on
encoded honest proofs (useful when M3 derives proof length via `encLength` from the canonical bound). -/
theorem proof_size_of_refines_enc
    (refines : Sampling.Quartet.LinkedQuartetRefinesEnc linkedSchedule enc s.scheme)
    (encBound : ∀ oracle message positions salts, positions.card = BATCH →
      (enc positions (honestCheckInput oracle message positions salts).proof).length ≤ proofBytes) :
    s.scheme.ProofSize proofBytes := by
  intro oracle message positions batch
  have eventEq :
      (fun result : Scheme.HonestResult => result.proofBytes ≤ proofBytes) <$>
        s.scheme.honest oracle message positions =
      (fun view : Commitment × Proof => view.2.length ≤ proofBytes) <$>
        fixedOracleRun oracle (executableTranscript s.scheme message positions) := by
    simp only [Scheme.honest, executableTranscript, fixed_oracle_run_bind,
      fixed_oracle_run_pure, map_bind, map_pure]
    simp only [fixedOracleRun, bind_map_left]
  rw [eventEq, (refines oracle message positions).prEvent_eq]
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro view reached
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨key, _, rfl⟩ := reached
  exact encBound oracle message positions
    (Permutation.LinkedSalt.salts linkedSchedule oracle.permutation key) batch

private theorem honest_check_event_enc (scheme : Scheme) (oracle : Oracle) (message : Message)
    (positions : Positions) :
    (fun result : Scheme.HonestResult => result.accepted = true) <$> scheme.honest oracle message positions =
      (fun view : Commitment × Proof =>
        (oracle.eval (scheme.check view.1 positions (message.restrict positions) view.2)).1 = true) <$>
        fixedOracleRun oracle (executableTranscript scheme message positions) := by
  simp only [Scheme.honest, executableTranscript, fixed_oracle_run_bind,
    fixed_oracle_run_pure, map_bind, map_pure]
  simp only [fixedOracleRun, bind_map_left]

set_option linter.constructorNameAsVariable false in
/-- Completeness for a re-encoded proof layout from `OpeningFactsEnc` and `CheckerFactsEnc`. -/
theorem completeness_enc (opens : OpeningFactsEnc enc s openingCycles proofBytes)
    (checks : CheckerFactsEnc enc s) : s.scheme.Completeness := by
  intro oracle message positions
  rw [honest_check_event_enc]
  rw [(opens.refines oracle message positions).prEvent_eq]
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro view reached
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
  obtain ⟨key, _, rfl⟩ := reached
  let salts := Permutation.LinkedSalt.salts linkedSchedule oracle.permutation key
  let input := honestCheckInputEnc enc oracle message positions salts
  change (oracle.eval (s.scheme.check input.commitment input.positions input.values input.proof)).1 = true
  rw [scheme_check_observation_enc]
  dsimp only
  erw [checks.honestAccepted oracle message positions salts]
  rfl

/-- Completeness directly from M1's decoder-side `CheckerFactsDec`, using round-trip and length
preservation of `enc` on honest proofs plus admission of canonical honest proofs. -/
theorem completeness_of_dec {dec : Positions → Proof → Proof}
    (opens : OpeningFactsEnc enc s openingCycles proofBytes)
    (checks : CheckerFactsDec dec s)
    (roundTrip : ∀ oracle message positions salts,
      dec positions (enc positions (honestCheckInput oracle message positions salts).proof) =
        (honestCheckInput oracle message positions salts).proof)
    (encLength : ∀ oracle message positions salts,
      (enc positions (honestCheckInput oracle message positions salts).proof).length =
        (honestCheckInput oracle message positions salts).proof.length)
    (honestFits : ∀ oracle message positions salts,
      (honestCheckInput oracle message positions salts).proof.length ≤ s.sizes.proof) :
    s.scheme.Completeness :=
  completeness_enc opens (checker_facts_enc_of_dec_length dec enc s checks roundTrip encLength honestFits)

include commit in
/-- Full certificate assembly for a re-encoded proof layout (matching `certificate_of_facts`'s
signature). -/
theorem certificate_of_facts_enc (admitted : s.Admission)
    (opens : OpeningFactsEnc enc s openingCycles proofBytes)
    (checks : CheckerFactsEnc enc s)
    (privateView : s.scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120))) :
    Certificate s proofBytes commitCycles openingCycles where
  admission := admitted
  machineSuccess := machine_success_enc commit opens
  termination := termination_enc commit opens checks
  completeness := completeness_enc opens checks
  honestBudgets := honest_budgets_enc commit opens checks
  proofSize := proof_size_enc opens
  proverCycles := prover_cycles_enc commit opens
  binding := checks.binding
  hidingProperty := privateView

include commit in
/-- Full certificate assembly deriving `Hiding` automatically from `opens.refines`. -/
theorem certificate_of_linked_enc (admitted : s.Admission)
    (opens : OpeningFactsEnc enc s openingCycles proofBytes)
    (checks : CheckerFactsEnc enc s) :
    Certificate s proofBytes commitCycles openingCycles :=
  certificate_of_facts_enc commit admitted opens checks
    (Sampling.Quartet.scheme_hiding_of_linked_enc linkedSchedule enc s.scheme opens.refines)

include commit in
/-- End-to-end M1+M2+M3 closing entry point: derives `Certificate` from `OpeningFactsEnc`,
M1's `CheckerFactsDec`, honest round-trip `dec p (enc p old) = old`, and honest length match. -/
theorem certificate_of_dec {dec : Positions → Proof → Proof}
    (admitted : s.Admission)
    (opens : OpeningFactsEnc enc s openingCycles proofBytes)
    (checks : CheckerFactsDec dec s)
    (roundTrip : ∀ oracle message positions salts,
      dec positions (enc positions (honestCheckInput oracle message positions salts).proof) =
        (honestCheckInput oracle message positions salts).proof)
    (encLength : ∀ oracle message positions salts,
      (enc positions (honestCheckInput oracle message positions salts).proof).length =
        (honestCheckInput oracle message positions salts).proof.length)
    (honestFits : ∀ oracle message positions salts,
      (honestCheckInput oracle message positions salts).proof.length ≤ s.sizes.proof) :
    Certificate s proofBytes commitCycles openingCycles :=
  certificate_of_linked_enc commit admitted opens
    (checker_facts_enc_of_dec_length dec enc s checks roundTrip encLength honestFits)

/-! ### 4. Identity Sanity Instances (`enc := fun _ proof => proof`) -/

theorem opening_facts_enc_id (s : Submission) (openingCycles proofBytes : Nat) :
    OpeningFactsEnc (fun _ proof => proof) s openingCycles proofBytes ↔
      OpeningFacts s openingCycles proofBytes := by
  constructor
  · intro h
    exact ⟨h.runs, (Sampling.Quartet.linked_quartet_refines_enc_id linkedSchedule s.scheme).mp h.refines⟩
  · intro h
    exact ⟨h.runs, (Sampling.Quartet.linked_quartet_refines_enc_id linkedSchedule s.scheme).mpr h.refines⟩

theorem linked_refines_of_parts_from_enc (scheme : Scheme)
    (root : Oracle → Message → Key → Commitment) (stash : Oracle → Message → Key → scheme.Trapdoor)
    (proofOf : Oracle → scheme.Trapdoor → Positions → Proof)
    (commits : ∀ o m, fixedOracleRun o (scheme.commit m) =ᵈ
      (do let k ← $ᵗ Key; pure (root o m k, stash o m k)))
    (opens : ∀ o td p, fixedOracleRun o (scheme.opening td p) = pure (proofOf o td p))
    (rootEq : ∀ o m k p, root o m k = (Sampling.Quartet.honestView Sampling.Quartet.builder o.compression
      (BiPermutation.equiv Block o.permutation) m p (Permutation.LinkedSalt.salts linkedSchedule o.permutation k)).1)
    (proofEq : ∀ o m k p, proofOf o (stash o m k) p = (Sampling.Quartet.honestView Sampling.Quartet.builder
      o.compression (BiPermutation.equiv Block o.permutation) m p
      (Permutation.LinkedSalt.salts linkedSchedule o.permutation k)).2) :
    Sampling.Quartet.LinkedQuartetRefines linkedSchedule scheme :=
  (Sampling.Quartet.linked_quartet_refines_enc_id linkedSchedule scheme).mp
    (linked_refines_of_parts_enc scheme (fun _ proof => proof) root stash proofOf commits opens rootEq proofEq)

theorem completeness_from_enc (opens : OpeningFacts s openingCycles proofBytes)
    (checks : CheckerFacts s) : s.scheme.Completeness :=
  completeness_enc
    ((opening_facts_enc_id s openingCycles proofBytes).mpr opens)
    ((checker_facts_enc_id s).mpr checks)

include commit in
theorem certificate_of_facts_from_enc (admitted : s.Admission)
    (opens : OpeningFacts s openingCycles proofBytes) (checks : CheckerFacts s)
    (privateView : s.scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120))) :
    Certificate s proofBytes commitCycles openingCycles :=
  certificate_of_facts_enc commit admitted
    ((opening_facts_enc_id s openingCycles proofBytes).mpr opens)
    ((checker_facts_enc_id s).mpr checks)
    privateView

end TwoPermutationPrototype.QuartetCounterCertificate
