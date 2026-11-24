import CommitGolfCandidate.NonceChainSecurity
import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.TwoPermutationTranscript
import CommitGolf.Statements
import CommitGolfCandidate.TwoPermutationCheckerReplay
import CommitGolfCandidate.CountingCoins
import CommitGolfCandidate.Machine
import CommitGolfCandidate.HonestSevenCodec
import CommitGolfCandidate.HeadStreamZero

namespace TwoPermutationPrototype.PackedCertificate
open CommitGolf CommitGolf.Riscv CommitGolfCandidate OracleComp TwoPermutationPrototype.Sampling

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

local instance {α : Type} : MeasurableSpace α := ⊤

structure OpeningFacts (s : Submission) : Prop where
  runs : ∀ (trapdoor : s.scheme.Trapdoor) (positions : Positions), ∃ result : Execution,
    s.run .opening (trapdoor, positions) = pure result ∧ result.exit = .success ∧
    s.openingSucceeded result = true ∧
    (positions.card = BATCH → result.cycles ≤ 679995 ∧ (s.readProof result).length ≤ 66672)
  refines : ChainTranscriptRefines s.scheme packedBuilder

/-- The honest input in the unpacked layout that the checker body analyses after unpacking. -/
def honestCheckInput (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) : CheckInput :=
  let view := pinnedHonestView (transcriptBuilder true) oracle.compression
    (BiPermutation.equiv Block oracle.permutation) message positions salts
  ⟨view.1, positions, message.restrict positions, view.2⟩

/-- The honest input the scheme delivers: the honest proof in packed form. -/
def packedHonestCheckInput (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) : CheckInput :=
  let view := pinnedHonestView packedBuilder oracle.compression
    (BiPermutation.equiv Block oracle.permutation) message positions salts
  ⟨view.1, positions, message.restrict positions, view.2⟩

theorem packed_honest_input (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    packedHonestCheckInput oracle message positions salts =
      { honestCheckInput oracle message positions salts with
        proof := ProofCodec.HeadStreamSeven.pack positions.card (honestCheckInput oracle message positions salts).proof } :=
  rfl

/-- Record-head facts of one honest run's unpacked transcript (`HonestCodec.HeadFacts`): every
opened salt has byte 15 below 8 and every opened record's leaf sibling has byte 30 below 32 and
byte 31 zero. Codec v2 needs them to round-trip the honest proof. They are not yet established
for this transcript (salts are 128-bit and leaf digests 256-bit here), so they are carried as a
hypothesis. -/
def HonestHeads (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape) : Prop :=
  HonestCodec.HeadFacts oracle.compression positions (fun index => salts index.val)
    (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)

/-- Salt tapes as the commitment stores them: every salt masked to its low 121 bits. -/
def MaskedSalts (salts : CompleteSaltTape) : Prop := ∀ i, Sampling.maskSalt (salts i) = salts i

/-- `HonestHeads` for every oracle, message, position set and masked salt tape. -/
def HonestHeadFacts : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape),
    MaskedSalts salts → HonestHeads oracle message positions salts

theorem masked_salt_small (salt : BitVec 128) : (Sampling.maskSalt salt).toNat < 2^121 := by
  unfold Sampling.maskSalt Sampling.saltMask
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num)

/-- Masked salts are below `2^121` and packed leaves are 238-bit, so the head facts hold. -/
theorem honest_head_facts : HonestHeadFacts := by
  intro oracle message positions salts masked
  apply HonestCodec.head_facts_of_small_salts
  intro index
  rw [← masked index.val]
  exact lt_trans (masked_salt_small _) (by norm_num)

theorem honest_unpack (heads : HonestHeadFacts) (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (masked : MaskedSalts salts) :
    ProofCodec.unpack positions.card
        (ProofCodec.pack positions.card (honestCheckInput oracle message positions salts).proof) =
      some (honestCheckInput oracle message positions salts).proof :=
  HonestCodec.honest_unpack_pack oracle.compression positions (fun index => salts index.val)
    (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)
    (heads oracle message positions salts masked)

theorem honest_tail_restore (heads : HonestHeadFacts) (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (masked : MaskedSalts salts) :
    ProofCodec.HeadStreamSeven.restore positions.card (packedHonestCheckInput oracle message positions salts).proof=
      ProofCodec.HeadStreamZero.pack positions.card (honestCheckInput oracle message positions salts).proof := by
  obtain ⟨b,len,hb,top,headBytes⟩ := HonestCodec.honest_codec_shape oracle.compression positions
    (fun index => salts index.val) (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)
  obtain ⟨salt,leaf,tail,leafTop⟩ := headBytes (heads oracle message positions salts masked)
  apply ProofCodec.HeadStreamSeven.restore_pack positions.card b _ len ?_ leaf
  apply HonestCodec.honest_record_salt121
  intro index
  rw [← masked index.val]
  exact masked_salt_small _

theorem honest_restore (heads : HonestHeadFacts) (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) (masked : MaskedSalts salts) :
    ProofCodec.HeadStreamZero.restore positions.card
      (ProofCodec.HeadStreamSeven.restore positions.card (packedHonestCheckInput oracle message positions salts).proof)=
      ProofCodec.pack positions.card (honestCheckInput oracle message positions salts).proof := by
  obtain ⟨b,len,hb,top,headBytes⟩ := HonestCodec.honest_codec_shape oracle.compression positions
    (fun index => salts index.val) (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)
  obtain ⟨salt,leaf,tail,leafTop⟩ := headBytes (heads oracle message positions salts masked)
  rw [honest_tail_restore heads oracle message positions salts masked]
  exact ProofCodec.HeadStreamZero.restore_pack positions.card b _ len leaf tail

structure CheckerFacts (s : Submission) : Prop where
  terminates : ∀ oracle input, (Checker.checkObservation s oracle input).1.1.exit ≠ .unfinished
  queryBudget : ∀ oracle input, (Checker.checkObservation s oracle input).2 ≤ 100*input.positions.card
  binding : s.scheme.Binding
  honestAccepted : ∀ oracle message positions salts, MaskedSalts salts →
    (Checker.checkObservation s oracle (packedHonestCheckInput oracle message positions salts)).1.1.exit = .success

variable {s : Submission} {commitCycles : Nat}
variable (commit : ∀ (message : Message) (result : Execution), result ∈ support (s.run .commit message) →
  result.exit = .success ∧ result.cycles = commitCycles ∧ result.oracleCalls ≤ COMMIT_BUDGET)

private theorem scheme_check_observation (oracle : Oracle) (input : CheckInput) :
    oracle.eval (s.scheme.check input.commitment input.positions input.values input.proof) =
      let observed := Checker.checkObservation s oracle input
      (observed.1.1.exit == .success, observed.2) := by
  rw [scheme_check_evaluation]
  have erase := Checker.check_record_erase oracle (s.run .check input)
  rw [← erase]
  rfl

private theorem counted_check_observation (oracle : Oracle) (input : CheckInput) :
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
  · have run : s.run .check input = pure ⟨.failure,initialMachine,0,0⟩ := by
      simp only [Submission.run, valid, decide_false, Bool.false_eq_true, ite_false]
    erw [run, oracle_run_pure, check_evaluation_pure]

include commit in
private theorem scheme_commit_budget (oracle : Oracle) (message : Message)
    (result : (Commitment × s.scheme.Trapdoor) × Nat)
    (reached : result ∈ support (oracle.run (s.scheme.commit message))) :
    result.2 ≤ COMMIT_BUDGET := by
  change result ∈ support (oracle.run (s.readCommit <$> s.run .commit message)) at reached
  rw [oracle_run_map oracle s.readCommit, support_map] at reached
  obtain ⟨execution,execReached,same⟩ := reached
  have actual := commit message execution.1 (writer_support (oracle.world.withAddCost Oracle.callCost) _ execution execReached)
  have calls := execute_counted_with_coins oracle (s.image .commit) (s.steps .commit)
    (s.initialState .commit message) true execution execReached
  have equal : execution.2 = result.2 := congrArg Prod.snd same
  rw [← equal, ← calls]
  exact actual.2.2

private theorem opening_run (opens : OpeningFacts s) (trapdoor : s.scheme.Trapdoor) (positions : Positions)
    (opened : Execution) (reached : opened ∈ support (s.run .opening (trapdoor,positions))) :
    opened.exit = .success ∧ s.openingSucceeded opened = true ∧
    (positions.card = BATCH → opened.cycles ≤ 679995 ∧ (s.readProof opened).length ≤ 66672) := by
  obtain ⟨result, exactRun, facts⟩ := opens.runs trapdoor positions
  rw [exactRun,support_pure,Set.mem_singleton_iff] at reached
  rwa [reached]

include commit in
private theorem honest_machine_resources (opens : OpeningFacts s) (message : Message) (positions : Positions)
    (result : MachineResult) (reached : result ∈ support (s.honestMachine message positions)) :
    result.success = true ∧
      (positions.card = BATCH → result.commitCycles ≤ commitCycles ∧ result.openingCycles ≤ 679995) := by
  change result ∈ support (do
    let committed ← s.run .commit message
    let opened ← s.run .opening ((s.readCommit committed).2,positions)
    pure ⟨committed.exit == Exit.success && s.openingSucceeded opened,
      committed.cycles,opened.cycles,(s.readProof opened).length⟩) at reached
  simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨committed,commitReached,opened,openReached,rfl⟩ := reached
  have finished := commit message committed commitReached
  have physical := opening_run opens (s.readCommit committed).2 positions opened openReached
  constructor
  · simp only [finished.1,beq_self_eq_true,physical.2.1,Bool.and_true]
  · intro batch
    exact ⟨finished.2.1.le,(physical.2.2 batch).1⟩

include commit in
theorem machine_success (opens : OpeningFacts s) : s.MachineSuccess := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (honest_machine_resources commit opens message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)).1

include commit in
theorem prover_cycles (opens : OpeningFacts s) : s.ProverCycles commitCycles 679995 := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (honest_machine_resources commit opens message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)).2 batch

include commit in
theorem termination (opens : OpeningFacts s) (checks : CheckerFacts s) : s.Termination := by
  intro oracle program input
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  have execution := writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached
  cases program with
  | commit =>
    rw [(commit input result.1 execution).1]
    decide
  | opening =>
    rw [(opening_run opens input.1 input.2 result.1 execution).1]
    decide
  | check =>
    erw [counted_check_observation oracle input] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact checks.terminates oracle input

private theorem scheme_open_run (trapdoor : s.scheme.Trapdoor) (positions : Positions)
    (result : Execution) (exactRun : s.run .opening (trapdoor,positions) = pure result) :
    s.scheme.opening trapdoor positions = pure (s.readProof result) := by
  change s.readProof <$> s.run .opening (trapdoor,positions) = _
  rw [exactRun,map_pure]

include commit in
theorem honest_budgets (opens : OpeningFacts s) (checks : CheckerFacts s) : s.scheme.HonestBudgets := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest,mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root,trapdoor⟩,calls⟩,committed,opened,opening,remainder⟩ := reached
  obtain ⟨openedMachine,exec,_⟩ := opens.runs trapdoor positions
  erw [scheme_open_run trapdoor positions openedMachine exec,oracle_run_pure] at opening
  simp only [support_pure,Set.mem_singleton_iff] at opening remainder
  subst opened
  subst result
  let input : CheckInput := ⟨root,positions,message.restrict positions,s.readProof openedMachine⟩
  have checked : (oracle.eval (s.scheme.check input.commitment input.positions input.values input.proof)).2 ≤
      100*positions.card := by
    rw [scheme_check_observation]
    exact checks.queryBudget oracle input
  exact ⟨scheme_commit_budget commit oracle message _ committed,Nat.zero_le _,checked⟩

theorem proof_size (opens : OpeningFacts s) : s.scheme.ProofSize 66672 := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest,mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root,trapdoor⟩,calls⟩,_,opened,opening,remainder⟩ := reached
  obtain ⟨openedMachine,exec,_,_,scored⟩ := opens.runs trapdoor positions
  erw [scheme_open_run trapdoor positions openedMachine exec,oracle_run_pure] at opening
  simp only [support_pure,Set.mem_singleton_iff] at opening remainder
  subst opened
  subst result
  exact (scored batch).2

private theorem honest_check_event (scheme : Scheme) (oracle : Oracle) (message : Message) (positions : Positions) :
    (fun result : Scheme.HonestResult => result.accepted = true) <$> scheme.honest oracle message positions =
      (fun view : Commitment × Proof =>
        (oracle.eval (scheme.check view.1 positions (message.restrict positions) view.2)).1 = true) <$>
        fixedOracleRun oracle (executableTranscript scheme message positions) := by
  simp only [Scheme.honest,executableTranscript,fixed_oracle_run_bind,
    fixed_oracle_run_pure,map_bind,map_pure]
  simp only [fixedOracleRun,bind_map_left]

set_option linter.constructorNameAsVariable false in
theorem completeness (opens : OpeningFacts s) (checks : CheckerFacts s) : s.scheme.Completeness := by
  intro oracle message positions
  rw [honest_check_event]
  rw [(opens.refines oracle message positions).prEvent_eq]
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro view reached
  simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨key,_,rfl⟩ := reached
  let salts := TwoPermutationPrototype.Sampling.maskedNonces oracle.permutation key
  let input := packedHonestCheckInput oracle message positions salts
  change (oracle.eval (s.scheme.check input.commitment input.positions input.values input.proof)).1 = true
  rw [scheme_check_observation]
  dsimp only
  erw [checks.honestAccepted oracle message positions salts (fun _ => Sampling.mask_salt_idem _)]
  rfl

include commit in
theorem certificate_of_facts (admitted : s.Admission) (opens : OpeningFacts s) (checks : CheckerFacts s)
    (privateView : s.scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120))) :
    Certificate s 66672 commitCycles 679995 where
  admission := admitted
  machineSuccess := machine_success commit opens
  termination := termination commit opens checks
  completeness := completeness opens checks
  honestBudgets := honest_budgets commit opens checks
  proofSize := proof_size opens
  proverCycles := prover_cycles commit opens
  binding := checks.binding
  hidingProperty := privateView

end TwoPermutationPrototype.PackedCertificate
