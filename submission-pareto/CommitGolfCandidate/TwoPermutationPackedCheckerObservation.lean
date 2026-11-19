import CommitGolfCandidate.TwoPermutationPackedCheckerBody
import CommitGolfCandidate.TwoPermutationPackedHeaderAssembly
import CommitGolfCandidate.TwoPermutationPackedTrustedInput
import CommitGolfCandidate.HeadStreamCheckUnpack

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (checkObservation check_recorded_map checker_positions_bound RecordInputFrame)
open TwoPermutationPrototype.PackedCertificate (honestCheckInput packedHonestCheckInput packed_honest_input honest_unpack
  HonestHeadFacts MaskedSalts)
open TwoPermutationPrototype.PackedHonest (honest_input_empty honest_input_records_fit honest_input_admitted
  honest_proof_length)
open HeadRestore (restoredInput converted_unpack converted_reject restored_steps_bound)
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000

theorem artifact_image :
    PackedChecker.submission.image .check = packedImage := by
  unfold PackedChecker.submission Artifact.submission packedImage
  rfl

attribute [local irreducible] execute checkEvaluation

/-- The facts about one checker run on a delivered (packed) input: those of the inner analysis,
with honesty stated for the packed honest input. -/
structure PackedObservationFacts (oracle : Oracle) (input : CheckInput)
    (observed : (Execution × List PublicRow) × Nat) : Prop where
  terminates : observed.1.1.exit ≠ .unfinished
  queries : observed.2 ≤ 26*input.positions.card
  paths : observed.1.1.exit = .success → ∀ index : {i // i ∈ input.positions},
    Nonempty (ProjectedOpening oracle index.val (input.values index) input.commitment observed.1.2)
  honest : ∀ message salts, MaskedSalts salts → input = packedHonestCheckInput oracle message input.positions salts →
    observed.1.1.exit = .success


private theorem observation_admitted (oracle : Oracle) (input : CheckInput)
    (admitted : input.proof.length ≤ PackedChecker.submission.sizes.proof) :
    checkObservation PackedChecker.submission oracle input =
      checkEvaluation oracle (recordRows
        (execute packedImage 1099511627776 (Assembly.submission.initialState .check input) false)) := by
  unfold checkObservation
  erw [PackedChecker.check_run_admitted input admitted, artifact_image, PackedChecker.initial_state]

private theorem observation_oversized (oracle : Oracle) (input : CheckInput)
    (oversized : PackedChecker.submission.sizes.proof < input.proof.length) :
    checkObservation PackedChecker.submission oracle input = ((⟨.failure,initialMachine,0,0⟩,[]),0) := by
  unfold checkObservation
  erw [PackedChecker.check_run_oversized input oversized]
  rw [record_rows_pure,check_evaluation_pure]

private abbrev rawObserved (oracle : Oracle) (input : CheckInput) :=
  checkEvaluation oracle (recordRows
    (execute packedImage 1099511627776 (Assembly.submission.initialState .check input) false))

private abbrev innerObserved (oracle : Oracle) (fuel : Nat) (m : MachineState) :=
  checkEvaluation oracle (recordRows (execute packedImage fuel m false))

section
variable [UnpackOrigin]

private theorem inner_empty (oracle : Oracle) (input : CheckInput) (m : MachineState) (view : UnpackedView input m)
    (fits : input.proof.length ≤ 2^33) (empty : input.positions.card = 0) (fuel : Nat) (enough : 6 ≤ fuel) :
    CheckerObservationFacts oracle input (innerObserved oracle fuel m) := by
  obtain ⟨result, executed, terminal, succeeds⟩ := header_empty input m view fits empty fuel enough
  unfold innerObserved
  rw [executed, record_rows_pure, check_evaluation_pure]
  refine ⟨terminal,Nat.zero_le _,?_,?_⟩
  · intro _ index
    have nonempty := Finset.card_pos.mpr ⟨index.val,index.property⟩
    omega
  · intro message salts canonical
    apply succeeds
    exact canonical.symm ▸ honest_input_empty oracle message input.positions salts empty

private theorem inner_short (oracle : Oracle) (input : CheckInput) (m : MachineState) (view : UnpackedView input m)
    (fits : input.proof.length ≤ 2^33) (short : input.proof.length < 498*input.positions.card)
    (fuel : Nat) (enough : 4 ≤ fuel) :
    CheckerObservationFacts oracle input (innerObserved oracle fuel m) := by
  obtain ⟨result,executed,failed⟩ := header_short input m view fits short fuel enough
  unfold innerObserved
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
    have required : 498*input.positions.card ≤ input.proof.length :=
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

private theorem inner_positive (record : Oracle → Nat → Index → MachineState → RecordBlock)
    (verified : RecordRefines record)
    (cap : ∀ (oracle : Oracle) (input : CheckInput), input.positions.card ≠ 0 →
      ∀ state rows rest, 25056 ≤ rest → RecordCursor input input.positions.card state →
      RecordInputFrame input input.positions.card state →
      CollectedTable oracle input input.positions.card state rows → CheckerCapFacts oracle input state rest)
    (oracle : Oracle) (input : CheckInput) (m : MachineState) (view : UnpackedView input m)
    (fits : input.proof.length ≤ 2^33) (nonempty : input.positions.card ≠ 0)
    (long : 498*input.positions.card ≤ input.proof.length) (fuel : Nat) (enough : 34359803903 ≤ fuel) :
    CheckerObservationFacts oracle input (innerObserved oracle fuel m) := by
  obtain ⟨state,cursor,memory,executeHeader⟩ := header_positive input m view fits nonempty long
  have cardinal := checker_positions_bound input
  have room : 2048*input.positions.card+25056 ≤ fuel-20 := by omega
  have initialFrame : RecordInputFrame input 0 state := by
    intro word _ _
    exact memory word
  have table := collected_table_empty oracle input state memory
  have body := checker_body_facts record verified oracle input state ⟨long,fits⟩ cursor initialFrame table
    (fuel-20) room (cap oracle input nonempty)
  have chain := observation_hop oracle input m state 20 20 (fuel-20) executeHeader body
  unfold innerObserved
  rwa [show 20+(fuel-20) = fuel by omega] at chain

private theorem packed_observation_hop (oracle : Oracle) (input : CheckInput)
    (before after : MachineState) (steps cycles fuel : Nat) (hop : Hop before after steps cycles)
    (body : PackedObservationFacts oracle input
      (checkEvaluation oracle (recordRows (execute packedImage fuel after false)))) :
    PackedObservationFacts oracle input
      (checkEvaluation oracle (recordRows (execute packedImage (steps+fuel) before false))) := by
  rw [hop fuel,bind_pure_comp,check_recorded_map]
  exact ⟨body.terminates, body.queries, body.paths, body.honest⟩

/-- The checker after the unpacking wrapper: the original analysis, for the unpacked input. -/
private theorem inner_observation (record : Oracle → Nat → Index → MachineState → RecordBlock)
    (verified : RecordRefines record)
    (cap : ∀ (oracle : Oracle) (input : CheckInput), input.positions.card ≠ 0 →
      ∀ state rows rest, 25056 ≤ rest → RecordCursor input input.positions.card state →
      RecordInputFrame input input.positions.card state →
      CollectedTable oracle input input.positions.card state rows → CheckerCapFacts oracle input state rest)
    (oracle : Oracle) (input : CheckInput) (m : MachineState) (view : UnpackedView input m)
    (fits : input.proof.length ≤ 2^33) (fuel : Nat) (enough : 34359803903 ≤ fuel) :
    CheckerObservationFacts oracle input (innerObserved oracle fuel m) := by
  by_cases empty : input.positions.card = 0
  · exact inner_empty oracle input m view fits empty fuel (by omega)
  by_cases short : input.proof.length < 498*input.positions.card
  · exact inner_short oracle input m view fits short fuel (by omega)
  exact inner_positive record verified cap oracle input m view fits empty (Nat.le_of_not_gt short) fuel enough

theorem unpack_packed_honest (heads : HonestHeadFacts) (oracle : Oracle) (message : Message)
    (positions : Positions) (salts : CompleteSaltTape) (masked : MaskedSalts salts) :
    unpackInput (restoredInput (packedHonestCheckInput oracle message positions salts)) =
      honestCheckInput oracle message positions salts := by
  unfold unpackInput
  change ({ restoredInput (packedHonestCheckInput oracle message positions salts) with
    proof := (ProofCodec.unpack positions.card
      (ProofCodec.HeadStreamZero.restore positions.card (packedHonestCheckInput oracle message positions salts).proof)).getD
        (restoredInput (packedHonestCheckInput oracle message positions salts)).proof } : CheckInput) = _
  rw [PackedCertificate.honest_restore heads _ _ _ _ masked,honest_unpack heads _ _ _ _ masked, Option.getD_some]
  rfl

private theorem padded_honest_le (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    (ProofCodec.pack positions.card (honestCheckInput oracle message positions salts).proof).length≤
      (honestCheckInput oracle message positions salts).proof.length := by
  by_cases empty : positions.card=0
  · rw [ProofCodec.pack_length,honest_input_empty oracle message positions salts empty,empty]
    decide
  · rw [ProofCodec.pack_length,honest_proof_length]
    unfold PackedOpening.proofLength PackedOpening.recordBytes ProofCodec.unpackedCount
      ProofCodec.packedLength ProofCodec.bodyLength
    omega

private theorem packed_honest_admitted (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    (packedHonestCheckInput oracle message positions salts).proof.length ≤
      PackedChecker.submission.sizes.proof := by
  have padded := padded_honest_le oracle message positions salts
  have admitted := honest_input_admitted oracle message positions salts
  change (ProofCodec.HeadStreamZero.pack positions.card (honestCheckInput oracle message positions salts).proof).length≤_
  rw [ProofCodec.HeadStreamZero.pack_length]
  unfold ProofCodec.HeadStreamZero.packedLength
  rw [ProofCodec.pack_length] at padded
  omega

private theorem wf_of_unpack {k : Nat} {Q P : Proof} (h : ProofCodec.unpack k Q = some P) :
    ProofCodec.WellFormed k Q.length := by
  unfold ProofCodec.unpack at h
  split_ifs at h with w
  exact w

private theorem packed_honest_virtual (heads : HonestHeadFacts) (oracle : Oracle) (message : Message)
    (positions : Positions) (salts : CompleteSaltTape) (masked : MaskedSalts salts) :
    let n := (packedHonestCheckInput oracle message positions salts).proof.length+positions.card
    n≤8355061248 ∧ ProofCodec.WellFormed positions.card n := by
  have length := congrArg List.length (PackedCertificate.honest_restore heads oracle message positions salts masked)
  simp only [ProofCodec.HeadStreamZero.restore_length,ProofCodec.HeadStreamZero.expandedLength] at length
  dsimp only
  rw [length]
  refine ⟨?_,wf_of_unpack (honest_unpack heads oracle message positions salts masked)⟩
  exact (padded_honest_le oracle message positions salts).trans (honest_input_admitted oracle message positions salts)

private theorem facts_transfer (heads : HonestHeadFacts) (oracle : Oracle) (input : CheckInput)
    (observed : (Execution × List PublicRow) × Nat)
    (inner : CheckerObservationFacts oracle (unpackInput (restoredInput input)) observed) :
    PackedObservationFacts oracle input observed := by
  refine ⟨inner.terminates, inner.queries, inner.paths, fun message salts masked canonical => ?_⟩
  apply inner.honest message salts
  exact (congrArg (fun v => unpackInput (restoredInput v)) canonical).trans
    (unpack_packed_honest heads oracle message input.positions salts masked)

end

private theorem raw_checker_observation (heads : HonestHeadFacts)
    (record : Oracle → Nat → Index → MachineState → RecordBlock)
    (verified : RecordRefines record)
    (cap : ∀ (oracle : Oracle) (input : CheckInput), input.positions.card ≠ 0 →
      ∀ state rows rest, 25056 ≤ rest → RecordCursor input input.positions.card state →
      RecordInputFrame input input.positions.card state →
      CollectedTable oracle input input.positions.card state rows → CheckerCapFacts oracle input state rest)
    (oracle : Oracle) (input : CheckInput) (fits : input.proof.length ≤ 8355061248) :
    PackedObservationFacts oracle input (rawObserved oracle input) := by
  letI : UnpackOrigin := ⟨(HeadRestore.headStart input).mem⟩
  unfold rawObserved
  by_cases good : input.proof.length+input.positions.card≤8355061248 ∧
      ProofCodec.WellFormed input.positions.card (input.proof.length+input.positions.card)
  · obtain ⟨t,hop,view⟩ := converted_unpack input fits good.1 good.2
    have prefixBound := restored_steps_bound input fits
    have bound := unpack_steps_bound _ _ good.2
    have wf : ProofCodec.WellFormed (restoredInput input).positions.card (restoredInput input).proof.length := by
      simpa only [HeadRestore.restored_positions,HeadRestore.restored_length] using good.2
    have oldFits : (restoredInput input).proof.length≤8355061248 := by
      simpa only [HeadRestore.restored_length] using good.1
    have sz := sizes_of (restoredInput input) wf oldFits
    let used := 2+HeadRestore.restoreSteps input.positions.card (input.proof.length+input.positions.card)+
      unpackSteps input.positions.card (input.proof.length+input.positions.card)
    have total : 1099511627776=used+(1099511627776-used) := by dsimp [used];omega
    rw [total]
    apply packed_observation_hop oracle input _ _ _ _ _ hop
    apply facts_transfer heads oracle input
    exact inner_observation record verified cap oracle (unpackInput (restoredInput input)) t view
      (by rw [unpack_input_length (restoredInput input) wf];have := sz.len;omega) _ (by dsimp [used];omega)
  · obtain ⟨steps,cycles,t,le,run⟩ := converted_reject input fits good
    have total : 1099511627776=steps+3+(1099511627776-steps-3) := by omega
    rw [total,run,record_rows_pure,check_evaluation_pure]
    refine ⟨?_, Nat.zero_le _, ?_, ?_⟩
    · change Exit.failure ≠ Exit.unfinished
      decide
    · intro impossible
      change Exit.failure = Exit.success at impossible
      cases impossible
    · intro message salts masked canonical
      apply (good ?_).elim
      rw [canonical]
      exact packed_honest_virtual heads oracle message input.positions salts masked

theorem checker_complete_observation (heads : HonestHeadFacts)
    (record : Oracle → Nat → Index → MachineState → RecordBlock)
    (verified : RecordRefines record)
    (cap : ∀ (oracle : Oracle) (input : CheckInput), input.positions.card ≠ 0 →
      ∀ state rows rest, 25056 ≤ rest → RecordCursor input input.positions.card state →
      RecordInputFrame input input.positions.card state →
      CollectedTable oracle input input.positions.card state rows → CheckerCapFacts oracle input state rest)
    (oracle : Oracle) (input : CheckInput) :
    PackedObservationFacts oracle input (checkObservation PackedChecker.submission oracle input) := by
  letI : UnpackOrigin := ⟨(HeadRestore.headStart input).mem⟩
  by_cases admitted : input.proof.length ≤ PackedChecker.submission.sizes.proof
  · rw [observation_admitted oracle input admitted]
    exact raw_checker_observation heads record verified cap oracle input admitted
  · rw [observation_oversized oracle input (Nat.lt_of_not_ge admitted)]
    refine ⟨by decide,Nat.zero_le _,?_,?_⟩
    · intro impossible
      cases impossible
    · intro message salts _ canonical
      exact (admitted (canonical.symm ▸ packed_honest_admitted oracle message input.positions salts)).elim

theorem checker_facts_of_observations (bound : PinnedReplayBound)
    (checked : ∀ (oracle : Oracle) (input : CheckInput),
      PackedObservationFacts oracle input (checkObservation PackedChecker.submission oracle input)) :
    PackedCertificate.CheckerFacts PackedChecker.submission := by
  refine ⟨fun oracle input => (checked oracle input).terminates,
    fun oracle input => (checked oracle input).queries.trans (by omega), ?_, ?_⟩
  · apply binding_of_packed_trace _ ?_ bound
    intro oracle input
    dsimp only
    intro accepted
    have count := (checked oracle input).queries
    have card := checker_positions_bound input
    exact ⟨by omega,(checked oracle input).paths accepted⟩
  · intro oracle message positions salts masked
    exact (checked oracle (packedHonestCheckInput oracle message positions salts)).honest message salts masked rfl

end TwoPermutationPrototype.Packed.Checker
