import CommitGolfCandidate.ChainedOpeningArtifact

/-! Actual delivered opening run, readProof, full-domain fuel and scored machine bounds. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
open CommitGolfCandidate.Permutation.NonceChain (Key)
set_option maxRecDepth 8192
set_option Elab.async false

theorem cached_packet_capacity (heap : Nat → BitVec 238) (salts : Index → BitVec 128) (positions : Positions) :
    (cachedEncodedPacket heap salts positions).length≤Artifact.submission.sizes.proof := by
  have cardinal : positions.card≤16777216 := by
    have bound : positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ positions
    exact bound
  have footer : InteriorCodec.footerBits (InteriorCodec.footerNodes positions)≤30208 := by
    unfold InteriorCodec.footerNodes
    split
    · simp [InteriorCodec.footerBits]
    · exact InteriorCodec.footer_bits_bound _
  rw [cached_encoded_length,InteriorCodec.proofLength]
  change 482*positions.card+(InteriorCodec.footerBits (InteriorCodec.footerNodes positions)+7)/8≤8355061248
  omega

theorem cached_opening_fuel (positions : Positions) (cycles : Nat)
    (bound : cycles≤2273*positions.card+66460+13*(openingNodes positions).length) :
    TwoPermutationPrototype.PackedOpening.scheduledCycles positions+cycles≤Artifact.submission.steps .opening := by
  have scheduled := TwoPermutationPrototype.PackedOpening.scheduled_fuel_fits positions
  have cardinal : positions.card≤16777216 := by
    have limit : positions.card≤LENGTH := by simpa [Index] using Finset.card_le_univ positions
    exact limit
  have nodes := opening_nodes_bound positions
  change TwoPermutationPrototype.PackedOpening.scheduledCycles positions+cycles≤549755813888
  omega

theorem read_proof_of_bytes (submission : Submission) (after : MachineState) (cycles : Nat) (packet : Proof)
    (base : submission.layout.proof=proofBase)
    (length : (after.getReg .x11).toNat=packet.length)
    (capacity : packet.length≤submission.sizes.proof)
    (bytes : BytesAt after (BitVec.ofNat 64 proofBase) packet) :
    submission.readProof ⟨.success,after,cycles,0⟩=packet := by
  have success : submission.openingSucceeded ⟨.success,after,cycles,0⟩=true := by
    simp [Submission.openingSucceeded,length,capacity]
  simp only [Submission.readProof,success,↓reduceIte,length]
  apply List.ext_getElem
  · simp
  · intro index _ inside
    simp only [List.getElem_map,List.getElem_range]
    rw [base,BitVec.ofNat_add,bytes index inside,List.getD_eq_getElem _ _ inside]

theorem opening_run_of_state (submission : Submission)
    (trapdoor : BitVec (8*submission.sizes.trapdoor)) (positions : Positions)
    (initial after : MachineState) (cycles : Nat)
    (entry : initial=submission.initialState .opening (trapdoor,positions))
    (budget : cycles≤submission.steps .opening)
    (ran : ∀ fuel coins, execute (submission.image .opening) (cycles+fuel) initial coins=
      pure ⟨.success,after,cycles,0⟩) :
    submission.run .opening (trapdoor,positions)=pure ⟨.success,after,cycles,0⟩ := by
  change execute (submission.image .opening) (submission.steps .opening)
    (submission.initialState .opening (trapdoor,positions)) true=_
  rw [←entry,show submission.steps .opening=cycles+(submission.steps .opening-cycles) by omega]
  exact ran _ true

private theorem artifact_proof_base : Artifact.submission.layout.proof=proofBase := rfl

private theorem artifact_opening_layout : OpeningLayout Artifact.submission := ⟨rfl,rfl,rfl,rfl⟩

private theorem artifact_opening_above : 8192≤dataBase (Artifact.submission.image .opening) := by decide +kernel

attribute [local irreducible] Artifact.submission Submission.run Submission.initialState Submission.readProof
attribute [local irreducible] deliveredSeedOutput deliveredReady

theorem artifact_opening_run (oracle : Oracle) (message : Message) (key : Key) (positions : Positions) :
    let trapdoor := (Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2
    let heap := referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
    let packet := cachedEncodedPacket heap (deliveredSalts oracle key) positions
    ∃ after cycles,
      Artifact.submission.run .opening (trapdoor,positions)=pure ⟨.success,after,cycles,0⟩ ∧
      Artifact.submission.readProof ⟨.success,after,cycles,0⟩=packet ∧
      cycles≤TwoPermutationPrototype.PackedOpening.scheduledCycles positions+
        (2273*positions.card+66460+13*(openingNodes positions).length) := by
  obtain ⟨after,cycles,ran,bytes,length,bound⟩ := artifact_cached_opening oracle message key positions
  have enough := cached_opening_fuel positions cycles bound
  refine ⟨after,TwoPermutationPrototype.PackedOpening.scheduledCycles positions+cycles,?_,?_,by omega⟩
  · exact opening_run_of_state Artifact.submission _ positions _ after _ rfl enough ran
  · exact read_proof_of_bytes Artifact.submission after
      (TwoPermutationPrototype.PackedOpening.scheduledCycles positions+cycles)
      (cachedEncodedPacket (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key)))
        (deliveredSalts oracle key) positions) artifact_proof_base length
      (cached_packet_capacity _ _ positions) bytes

theorem artifact_opening_scored (oracle : Oracle) (message : Message) (key : Key) (positions : Positions)
    (count : positions.card=BATCH) :
    let trapdoor := (Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2
    let heap := referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))
    let packet := cachedEncodedPacket heap (deliveredSalts oracle key) positions
    ∃ result : Execution, Artifact.submission.run .opening (trapdoor,positions)=pure result ∧
      result.exit=.success ∧ result.oracleCalls=0 ∧ result.cycles≤444579 ∧
      Artifact.submission.readProof result=packet ∧ packet.length≤65472 := by
  obtain ⟨after,cycles,ran,read,bound⟩ := artifact_opening_run oracle message key positions
  have scheduled := (TwoPermutationPrototype.PackedOpening.scheduled_scored_limits positions count).1
  have nodes := opening_nodes_bound positions
  have cardinal : positions.card=128 := count
  refine ⟨⟨.success,after,cycles,0⟩,ran,rfl,rfl,?_,read,?_⟩
  · change cycles≤444579
    omega
  · rw [cached_encoded_length]
    exact InteriorCodec.proof_length_bound positions (by omega)

theorem artifact_arbitrary_opening_run
    (trapdoor : BitVec (8*Artifact.submission.sizes.trapdoor)) (positions : Positions) :
    ∃ after cycles, Artifact.submission.run .opening (trapdoor,positions)=pure ⟨.success,after,cycles,0⟩ ∧
      cycles≤TwoPermutationPrototype.PackedOpening.scheduledCycles positions+
        (2273*positions.card+66460+13*(openingNodes positions).length) := by
  obtain ⟨before,ranPrefix,boundary⟩ := cached_prefix cachedControllerImage cached_controller_prefix
    Artifact.submission artifact_opening_layout artifact_opening_above trapdoor positions
  obtain ⟨after,cycles,ran,bound⟩ := cached_boundary_range_postpass trapdoor positions before boundary
  refine ⟨after,TwoPermutationPrototype.PackedOpening.scheduledCycles positions+cycles,?_,by omega⟩
  apply opening_run_of_state Artifact.submission trapdoor positions _ after _ rfl (cached_opening_fuel positions cycles bound)
  intro fuel coins
  rw [opening_manifest_image,Nat.add_assoc,execute_add,ranPrefix coins]
  simp only [pure_bind,resume,ite_true]
  rw [ran fuel coins]
  rfl

theorem artifact_opening_terminates
    (trapdoor : BitVec (8*Artifact.submission.sizes.trapdoor)) (positions : Positions) {result : Execution}
    (reached : result∈support (Artifact.submission.run .opening (trapdoor,positions))) :
    result.exit=.success := by
  obtain ⟨after,cycles,ran,_⟩ := artifact_arbitrary_opening_run trapdoor positions
  rw [ran,support_pure,Set.mem_singleton_iff] at reached
  subst result
  rfl

theorem artifact_honest_opening_resources (oracle : Oracle) (message : Message) (key : Key) (positions : Positions) :
    ∃ result : Execution,
      Artifact.submission.run .opening ((Artifact.submission.readCommit (deliveredSeedOutput oracle message key)).2,positions)=pure result ∧
      Artifact.submission.openingSucceeded result=true ∧ result.oracleCalls=0 ∧
      (positions.card=BATCH → result.cycles≤444579 ∧ (Artifact.submission.readProof result).length≤65472) := by
  obtain ⟨after,cycles,ran,bytes,length,bound⟩ := artifact_cached_opening oracle message key positions
  have exactRun := opening_run_of_state Artifact.submission _ positions _ after _ rfl
    (cached_opening_fuel positions cycles bound) ran
  let total := TwoPermutationPrototype.PackedOpening.scheduledCycles positions+cycles
  have capacity := cached_packet_capacity
    (referenceHeap oracle (pinnedLeafNodes oracle (deliveredReady oracle message key))) (deliveredSalts oracle key) positions
  have read := read_proof_of_bytes Artifact.submission after total _ artifact_proof_base length capacity bytes
  refine ⟨⟨.success,after,total,0⟩,exactRun,?_,rfl,?_⟩
  · simp only [Submission.openingSucceeded,length,capacity,decide_true,Bool.and_self,beq_self_eq_true]
  · intro batch
    have scheduled := (TwoPermutationPrototype.PackedOpening.scheduled_scored_limits positions batch).1
    have nodes := opening_nodes_bound positions
    have count : positions.card=128 := batch
    constructor
    · change total≤444579
      dsimp only [total]
      omega
    · rw [read,cached_encoded_length]
      exact InteriorCodec.proof_length_bound positions (by omega)

end CommitGolfCandidate.Chained.Native
