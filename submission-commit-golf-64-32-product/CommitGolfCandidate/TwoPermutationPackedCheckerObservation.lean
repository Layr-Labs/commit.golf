import CommitGolfCandidate.R1bHonestCarry
import CommitGolfCandidate.TwoPermutationPackedInputFrame
import CommitGolfCandidate.TwoPermutationPackedCheckerBody
import CommitGolfCandidate.TwoPermutationPackedHeaderAssembly
import CommitGolfCandidate.TwoPermutationPackedTrustedInput

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (checkObservation check_recorded_map checker_positions_bound)
open TwoPermutationPrototype.PackedCertificate (honestCheckInput)
open TwoPermutationPrototype.PackedHonest (honest_input_empty honest_input_records_fit honest_input_admitted)
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000

theorem artifact_image :
    PackedChecker.submission.image .check = packedImage := by
  exact delivered_check_image

attribute [local irreducible] execute checkEvaluation

private theorem observation_admitted (oracle : Oracle) (input : CheckInput)
    (admitted : input.proof.length ≤ PackedChecker.submission.sizes.proof) :
    checkObservation PackedChecker.submission oracle input =
      checkEvaluation oracle (recordRows
        (execute packedImage 34628239360 (Assembly.submission.initialState .check input) false)) := by
  unfold checkObservation
  erw [PackedChecker.check_run_admitted input admitted, artifact_image, PackedChecker.initial_state]

private theorem observation_oversized (oracle : Oracle) (input : CheckInput)
    (oversized : PackedChecker.submission.sizes.proof < input.proof.length) :
    checkObservation PackedChecker.submission oracle input = ((⟨.failure,initialMachine,0,0⟩,[]),0) := by
  unfold checkObservation
  erw [PackedChecker.check_run_oversized input oversized]
  rw [record_rows_pure,check_evaluation_pure]

private abbrev rawObserved (oracle : Oracle) (state : MachineState) (fuel : Nat) :=
  checkEvaluation oracle (recordRows (execute packedImage fuel state false))

private theorem raw_empty (oracle : Oracle) (input : CheckInput) {st : MachineState} (hdr : Header input st) (fuel : Nat) (budget : 34628229160≤fuel)
    (fits : input.proof.length ≤ 8388615680) (empty : input.positions.card = 0) :
    CheckerObservationFacts oracle input (rawObserved oracle st fuel) := by
  obtain ⟨result, executed, terminal, succeeds⟩ := header_empty hdr fuel (by omega) fits empty
  unfold rawObserved
  rw [executed, record_rows_pure, check_evaluation_pure]
  refine ⟨terminal,Nat.zero_le _,?_,?_⟩
  · intro _ index
    have nonempty := Finset.card_pos.mpr ⟨index.val,index.property⟩
    omega
  · intro message salts canonical
    apply succeeds
    exact canonical.symm ▸ honest_input_empty oracle message input.positions salts empty

private theorem raw_short (oracle : Oracle) (input : CheckInput) {st : MachineState} (hdr : Header input st) (fuel : Nat) (budget : 34628229160≤fuel)
    (fits : input.proof.length ≤ 8388615680) (short : input.proof.length < 500*input.positions.card) :
    CheckerObservationFacts oracle input (rawObserved oracle st fuel) := by
  obtain ⟨result,executed,failed⟩ := header_short hdr fuel (by omega) fits short
  unfold rawObserved
  rw [executed, record_rows_pure, check_evaluation_pure]
  refine ⟨?_,Nat.zero_le _,?_,?_⟩
  · change result.exit ≠ .unfinished
    rw [failed]
    decide
  · intro impossible
    change result.exit = .success at impossible
    rw [failed] at impossible
    cases impossible
  · intro message salts canonical
    have required : 500*input.positions.card ≤ input.proof.length :=
      canonical.symm ▸ honest_input_records_fit oracle message input.positions salts
    omega

private theorem observation_hop (oracle : Oracle) (input : CheckInput)
    (before after : MachineState) (steps cycles fuel : Nat) (hop : Hop before after steps cycles)
    (body : CheckerObservationFacts oracle input
      (checkEvaluation oracle (recordRows (execute packedImage fuel after false)))) :
    CheckerObservationFacts oracle input
      (checkEvaluation oracle (recordRows (execute packedImage (steps+fuel) before false))) := by
  rw [hop fuel,bind_pure_comp,check_recorded_map]
  exact body.charge cycles

private theorem raw_positive (record : Oracle → Nat → Index → MachineState → RecordBlock)
    (verified : RecordRefines record)
    (cap : ∀ (oracle : Oracle) (input : CheckInput), input.positions.card ≠ 0 →
      ∀ state rows rest, 25056 ≤ rest → RecordCursor input input.positions.card state →
      InputFrame input input.positions.card state →
      CollectedTable oracle input input.positions.card state rows → CheckerCapFacts oracle input state rest)
    (oracle : Oracle) (input : CheckInput) {st : MachineState} (hdr : Header input st) (fuel : Nat) (budget : 34628229160≤fuel) (fits : input.proof.length ≤ 8388615680)
    (nonempty : input.positions.card ≠ 0) (long : 500*input.positions.card ≤ input.proof.length) :
    CheckerObservationFacts oracle input (rawObserved oracle st fuel) := by
  obtain ⟨state,cursor,memory,executeHeader⟩ := header_positive hdr fits nonempty long
  have cardinal := checker_positions_bound input
  have enough : 2060*input.positions.card+25056 ≤ (fuel-21) := by omega
  have initialFrame : InputFrame input 0 state := by
    obtain ⟨tail,size,mem⟩:=hdr.input
    refine ⟨tail,size,?_⟩
    intro word bound used
    exact (congrFun memory (wordAddress word)).trans (mem word bound used)
  have table := collected_table_empty oracle input state (fun n hn=>(congrFun memory _).trans (hdr.marks n hn))
  have body := checker_body_facts record verified oracle input state ⟨long,fits⟩ cursor initialFrame table
    (fuel-21) enough (cap oracle input nonempty)
  have chain := observation_hop oracle input st state
    21 24 (fuel-21) executeHeader body
  simpa only [show 21+(fuel-21)=fuel by omega] using chain

private theorem raw_checker_observation (record : Oracle → Nat → Index → MachineState → RecordBlock)
    (verified : RecordRefines record)
    (cap : ∀ (oracle : Oracle) (input : CheckInput), input.positions.card ≠ 0 →
      ∀ state rows rest, 25056 ≤ rest → RecordCursor input input.positions.card state →
      InputFrame input input.positions.card state →
      CollectedTable oracle input input.positions.card state rows → CheckerCapFacts oracle input state rest)
    (oracle : Oracle) (input : CheckInput) {st : MachineState} (hdr : Header input st) (fuel : Nat) (budget : 34628229160≤fuel) (fits : input.proof.length ≤ 8388615680) :
    CheckerObservationFacts oracle input (rawObserved oracle st fuel) := by
  by_cases empty : input.positions.card = 0
  · exact raw_empty oracle input hdr fuel budget fits empty
  by_cases short : input.proof.length < 500*input.positions.card
  · exact raw_short oracle input hdr fuel budget fits short
  exact raw_positive record verified cap oracle input hdr fuel budget fits empty (Nat.le_of_not_gt short)

private theorem badNotHonest (x : CheckInput) (invalid : bad x) (o : Oracle) (m : Message) (s : CompleteSaltTape) :
    x ≠ PackedCertificate.wireCheckInput o m x.positions s := by
  intro honest
  rcases invalid with h | h
  all_goals
    unfold Route.ofInput at h
    split_ifs at h <;> try contradiction
    have batch : x.positions.card=BATCH := by change _=128;omega
    have len : (PackedCertificate.wireCheckInput o m x.positions s).proof.length=67489 := by rw [←honest];omega
    have tag:=PackedHonest.tagHonest o m x.positions s batch len
    rw [←honest] at tag
    unfold frontierCount at *;omega

structure WireFacts (oracle : Oracle) (input : CheckInput)
    (observed : (Execution × List PublicRow) × Nat) : Prop where
  terminates : observed.1.1.exit ≠ .unfinished
  queries : observed.2 ≤ 28*input.positions.card
  paths : observed.1.1.exit = .success → ∀ index : {i // i ∈ input.positions},
    Nonempty (Hybrid.ProjectedOpening oracle index.val (input.values index) input.commitment observed.1.2)
  honest : ∀ message salts, input = PackedCertificate.wireCheckInput oracle message input.positions salts →
    observed.1.1.exit = .success

theorem checker_complete_observation (record : Oracle → Nat → Index → MachineState → RecordBlock)
    (verified : RecordRefines record)
    (cap : ∀ (oracle : Oracle) (input : CheckInput), input.positions.card ≠ 0 →
      ∀ state rows rest, 25056 ≤ rest → RecordCursor input input.positions.card state →
      InputFrame input input.positions.card state →
      CollectedTable oracle input input.positions.card state rows → CheckerCapFacts oracle input state rest)
    (oracle : Oracle) (input : CheckInput) :
    WireFacts oracle input (checkObservation PackedChecker.submission oracle input) := by
  by_cases admitted : input.proof.length≤PackedChecker.submission.sizes.proof
  · rw [observation_admitted oracle input admitted]
    change WireFacts oracle input (checkEvaluation oracle (recordRows (execute packedImage 34628239360 (initial input) false)))
    by_cases fail : bad input
    · obtain ⟨v,ran,no⟩:=badRun input admitted fail
      rw [ran,record_rows_pure,check_evaluation_pure]
      refine ⟨by change v.exit≠.unfinished;rw [no];decide,Nat.zero_le _,?_,?_⟩
      · intro impossible;change v.exit=.success at impossible;rw [no] at impossible;contradiction
      · intro m salts same;exact (badNotHonest _ fail oracle m salts same).elim
    · obtain ⟨st,steps,cycles,limit,run,header⟩:=front input admitted fail
      let x:=wideInput input
      have fits : x.proof.length≤8388615680 := by
        change (Hybrid.wideProof _ _).length≤_
        unfold Hybrid.wideProof R1b.Carry.batchDecode
        split_ifs <;> first | exact admitted | (simp only [List.length_take,R1b.Carry.wide_length]; omega)
      have actual:=raw_checker_observation record verified cap oracle x header (34628239360-steps) (by omega) fits
      have hop : Hop (initial input) st steps cycles := by
        intro f
        rw [←delivered_check_image,Nat.add_comm steps f]
        exact run f false
      have res:=observation_hop oracle x _ st steps cycles (34628239360-steps) hop actual
      rw [show steps+(34628239360-steps)=34628239360 by omega] at res
      refine ⟨res.terminates,res.queries,res.paths,?_⟩
      intro m salts eq
      apply res.honest m salts
      exact (congrArg wideInput eq).trans (PackedHonest.wideWireInput oracle m input.positions salts)
  · rw [observation_oversized oracle input (Nat.lt_of_not_ge admitted)]
    refine ⟨by decide,Nat.zero_le _,?_,?_⟩
    · intro impossible;cases impossible
    · intro m salts eq
      have wide:=honest_input_admitted oracle m input.positions salts
      apply False.elim;apply admitted
      rw [eq]
      change (Hybrid.wireProof input.positions _).length≤_
      by_cases batch : input.positions.card=BATCH
      · exact (Hybrid.wireBound _ _ batch).trans (by decide)
      · simpa [Hybrid.wireProof,batch] using wide

theorem checker_facts_of_observations (bound : Hybrid.C3PReplayBound238)
    (checked : ∀ (oracle : Oracle) (input : CheckInput),
      WireFacts oracle input (checkObservation PackedChecker.submission oracle input)) :
    PackedCertificate.CheckerFacts PackedChecker.submission := by
  refine ⟨fun oracle input => (checked oracle input).terminates,
    fun oracle input => (checked oracle input).queries.trans (by omega), ?_, ?_⟩
  · apply Hybrid.binding_of_packed_trace _ ?_ bound
    intro oracle input
    dsimp only
    intro accepted
    have count := (checked oracle input).queries
    have card := checker_positions_bound input
    exact ⟨by omega,(checked oracle input).paths accepted⟩
  · intro oracle message positions salts
    exact (checked oracle (PackedCertificate.wireCheckInput oracle message positions salts)).honest message salts rfl

end TwoPermutationPrototype.Packed.Checker
