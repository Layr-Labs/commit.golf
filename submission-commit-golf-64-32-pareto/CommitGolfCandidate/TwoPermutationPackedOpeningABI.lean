import CommitGolfCandidate.TwoPermutationPackedOpeningInitial
import CommitGolfCandidate.TwoPermutationPackedOpeningFinish

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp Sampling
open Opening (OpeningLayout trapdoorBase proofBase groupsBefore openingNodes capDigestAddress)

/-- Unpacked opener cycles before the pack postpass (`scheduledCycles` minus the old 4-cycle
exit), plus the exit block and postpass. -/
def openingCycles (positions : Positions) : Nat :=
  scheduledCycles positions - 4 + Pack.exitCycles positions.card (openingNodes positions).length

/-- Instructions executed by the opener, including the pack postpass. -/
def openingSteps (positions : Positions) : Nat :=
  scheduledCycles positions - 4 + Pack.exitSteps positions.card (openingNodes positions).length

/-- Length of the delivered (packed) proof. -/
def packedProofLength (positions : Positions) : Nat :=
  ProofCodec.packedLength positions.card (15*positions.card + (openingNodes positions).length)

/-- Fuel that covers `openingSteps` for every position set. -/
def openingFuel : Nat := 235518697118

theorem opening_steps_fit (positions : Positions) : openingSteps positions ≤ openingFuel := by
  have cardinal : positions.card ≤ 16777216 := by
    have bound : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
    exact bound
  have scheduled := scheduled_fuel_fits positions
  have exit := Pack.exit_steps_le_cardinality positions.card _ cardinal (Opening.opening_nodes_bound positions)
  unfold openingSteps openingFuel
  omega

theorem packed_proof_le (positions : Positions) : packedProofLength positions ≤ proofLength positions := by
  unfold packedProofLength proofLength recordBytes ProofCodec.packedLength ProofCodec.bodyLength
  by_cases empty : positions.card = 0
  · simp [openingNodes, empty]
  · omega

structure OpeningABI (s : Submission) extends OpeningLayout s where
  image : s.image .opening = openingImage
  capacity : PackedOpening.capacity ≤ s.sizes.proof
  fuel : openingFuel ≤ s.steps .opening

/-- The opener halts with the packed proof: `before` is its state just before the pack postpass,
holding the unpacked records and footer digests, and the delivered bytes are `ProofCodec.pack` of
that state's `proofLength` bytes at `proofBase`. -/
structure OpenPhysical (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (result : Execution) : Prop where
  success : result.exit = .success
  length : (result.state.getReg .x11).toNat = packedProofLength positions
  noCalls : result.oracleCalls = 0
  cycles : result.cycles = openingCycles positions
  unpacked : ∃ before : MachineState,
    CompletedRecords s trapdoor positions before positions.card ∧
    (∀ i (inside : i < (openingNodes positions).length),
      readBuffer before (recordBase positions.card+30*i) 30 =
        (trapdoor.extractLsb' (256*(openingNodes positions)[i]) 256).extractLsb' 0 240) ∧
    ∀ p < packedProofLength positions,
      result.state.getByte (BitVec.ofNat 64 (proofBase + p)) =
        (ProofCodec.pack positions.card (proofBytes before (proofLength positions))).getD p 0

private theorem byte_memory (before after : MachineState) (address : Nat) (fit : address < MEMORY_BYTES)
    (frame : ∀ query : Nat, trapdoorBase ≤ query → query < 2^64 →
      after.getMem (BitVec.ofNat 64 query) = before.getMem (BitVec.ofNat 64 query))
    (above : trapdoorBase ≤ address) :
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address) := by
  let aligned := alignToDword (BitVec.ofNat 64 address)
  have safe : MEMORY_BYTES+8 ≤ 2^64 := by decide
  have lower := aligned_dword_above trapdoorBase address (by decide) above (by omega)
  have stable := frame aligned.toNat lower aligned.isLt
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at stable
  change extractByte (after.getMem aligned) _ = _
  rw [stable]
  rfl

attribute [local irreducible] execute capPreparation setupPrefix readBuffer

/-- `keeps` says that every run of the opener preserves `x16` (the position count); it is
`RegisterPreservation.execute_keeps_register openingImage .x16` once `imageAvoids openingImage .x16`
is checked. -/
theorem opening_physical_with (recordsExecute : RecordsExecute)
    (keeps : ∀ (steps : Nat) (state : MachineState) (coins : Bool),
      ∀ result ∈ support (execute openingImage steps state coins), result.state.getReg .x16 = state.getReg .x16)
    (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) :
    ∃ result : Execution, s.run .opening (trapdoor, positions) = pure result ∧ OpenPhysical s trapdoor positions result := by
  let initial := s.initialState .opening (trapdoor, positions)
  have countReg : initial.getReg .x16 = BitVec.ofNat 64 positions.card := rfl
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have budget : openingSteps positions ≤ s.steps .opening := (opening_steps_fit positions).trans abi.fuel
  have allFit := (Nat.add_le_add_left (proof_fits_every_cardinality positions) _).trans packed_proof_memory
  have proofPointer : initial.getReg .x15 = BitVec.ofNat 64 proofBase :=
    congrArg (BitVec.ofNat 64) abi.toOpeningLayout.proof
  by_cases empty : positions.card = 0
  · have noNodes : (openingNodes positions).length = 0 := by simp [openingNodes, empty]
    obtain ⟨final, ran, ret⟩ := execute_empty initial rfl (by rw [countReg, empty]) proofPointer
    have charge : scheduledCycles positions = 7 := by simp [scheduledCycles, empty]
    have stepsEq : openingSteps positions = 3 + Pack.exitSteps 0 0 := by
      unfold openingSteps; rw [charge, empty, noNodes]
    have cyclesEq : openingCycles positions = 3 + Pack.exitCycles 0 0 := by
      unfold openingCycles; rw [charge, empty, noNodes]
    have noBytes : packedProofLength positions = 0 := by
      unfold packedProofLength; rw [empty, noNodes]; rfl
    let result : Execution := ⟨.success, final, openingCycles positions, 0⟩
    refine ⟨result, ?_, ⟨rfl, ?_, rfl, rfl, ⟨initial, ?_, ?_, ?_⟩⟩⟩
    · change execute (s.image .opening) (s.steps .opening) initial true = pure result
      rw [abi.image, show s.steps .opening = 3 + Pack.exitSteps 0 0 + (s.steps .opening - openingSteps positions) by
        omega, ran]
      simp only [result, cyclesEq]
    · change (final.getReg .x11).toNat = _
      rw [ret, noBytes]
    · intro ordinal present _
      omega
    · intro i inside
      omega
    · intro p inside
      omega
  · let grouped := groupsBefore positions positions.card
    let nodes := capFrontierNodes grouped 1 8
    let dest := recordBase positions.card
    let begin := setupPrefix initial 13
    let lower := runRecords positions.card 0 positions.card begin
    let prepared := capPreparation lower
    have positive : 0 < positions.card := by omega
    have ready := opening_first_boundary s abi.toOpeningLayout trapdoor positions positive
    have marks := initial_record_marks s abi.toOpeningLayout abi.image trapdoor positions
    have assembled := recordsExecute s abi.toOpeningLayout trapdoor positions begin 0 positions.card
      (by omega) ready marks (fun j _ first => (by omega : False).elim)
    have atCap : RecordBoundary s trapdoor positions lower positions.card := by
      simpa only [Nat.zero_add] using assembled.boundary
    have written : CompletedRecords s trapdoor positions lower positions.card := by
      simpa only [Nat.zero_add] using assembled.bytes
    have groups : Opening.RecordMarks positions lower positions.card := by
      simpa only [Nat.zero_add] using assembled.marks
    have leafMarks (node : Nat) (leaf : 255 < node) (inside : node < 512) :
        Opening.machineMarks lower node = Opening.markWord grouped node := by
      rw [groups node inside, Opening.mark_word_leaf grouped ⟨node,inside⟩ (show 256 ≤ node by omega)]
    have ⟨rootPC, root⟩ := cap_preparation_context lower grouped dest
      atCap.marks atCap.capHeap atCap.capLeaves atCap.proofBegin atCap.dest leafMarks
    have frontier : openingNodes positions = nodes := by simp [openingNodes, empty, nodes, grouped]
    have room : dest+30*nodes.length ≤ MEMORY_BYTES := by
      simpa only [proofLength, frontier, dest, recordBase, Nat.add_assoc] using allFit
    have aligned : dest % 2 = 0 := by
      have base : proofBase % 2 = 0 := by decide
      unfold dest recordBase recordBytes
      omega
    have above : proofBase ≤ dest := by unfold dest recordBase; omega
    obtain ⟨after, ranCap, afterPC, endPosition, footerBytes⟩ :=
      cap_subtree grouped prepared 1 8 dest Opening.cap_span_root root rootPC above aligned room
    have charge : scheduledCycles positions = 13+(590*positions.card-1)+770+capSubtreeCycles grouped 1 8+8 := by
      rw [scheduledCycles, if_neg empty]
      dsimp only [grouped]
      omega
    have ranSetup : RunsOpeningBlock initial begin 13 :=
      fun fuel coins => execute_setup initial rfl fuel coins (countReg ▸ nonempty_count positions positive)
    have ranRecords : RunsOpeningBlock begin lower (590*positions.card-1) := by
      have charged : recordsCost positions.card 0 positions.card = 590*positions.card-1 := by
        simp [recordsCost, positive]
      exact charged ▸ assembled.run
    have ranPrep : RunsOpeningBlock lower prepared 770 :=
      execute_cap_preparation lower (by simpa using atCap.pc) atCap.marks
    have prefixTrace := ((ranSetup.next ranRecords).next ranPrep).next ranCap
    -- the position count survives every instruction before the exit block
    have afterCount : after.getReg .x16 = BitVec.ofNat 64 positions.card := by
      have trace := prefixTrace 0 true
      have reached : (⟨.unfinished, after, 13+(590*positions.card-1)+770+capSubtreeCycles grouped 1 8, 0⟩ :
          Execution) ∈ support (execute openingImage
            (13+(590*positions.card-1)+770+capSubtreeCycles grouped 1 8 + 0) initial true) := by
        rw [trace, show execute openingImage 0 after true = pure ⟨.unfinished, after, 0, 0⟩ by simp only [execute]]
        simp [Execution.charge]
      exact (keeps _ initial true _ reached).trans countReg
    have proofFit : 498*positions.card + 30*nodes.length ≤ Pack.capacityBytes := by
      have fits := proof_fits_every_cardinality positions
      have hcap : capacity = Pack.capacityBytes := by
        unfold capacity recordBytes Pack.capacityBytes LENGTH LOG_LENGTH; norm_num
      rw [hcap] at fits
      simp only [proofLength, frontier, recordBytes] at fits
      exact fits
    have lengthWord : after.getReg .x21 - after.getReg .x20 =
        BitVec.ofNat 64 (498*positions.card + 30*nodes.length) := by
      have big : proofBase + (498*positions.card + 30*nodes.length) < 2^64 := by
        have : MEMORY_BYTES < 2^64 := by decide
        have := room
        unfold dest recordBase recordBytes at this
        omega
      rw [endPosition.destWord, endPosition.context.proofStart,
        show dest + 30*nodes.length = proofBase + (498*positions.card + 30*nodes.length) by
          unfold dest recordBase recordBytes; omega,
        Pack.w_sub _ _ (by omega) big, Nat.add_sub_cancel_left]
    obtain ⟨final, ranExit, retLen, packedBytes, _⟩ := root_exit after afterPC endPosition.nodeWord
      positions.card nodes.length afterCount endPosition.context.proofStart lengthWord proofFit
    have stepsEq : openingSteps positions =
        13+(590*positions.card-1)+770+capSubtreeCycles grouped 1 8 + (4 + Pack.exitSteps positions.card nodes.length) := by
      unfold openingSteps; rw [charge, frontier]; omega
    have cyclesEq : openingCycles positions =
        13+(590*positions.card-1)+770+capSubtreeCycles grouped 1 8 + (4 + Pack.exitCycles positions.card nodes.length) := by
      unfold openingCycles; rw [charge, frontier]; omega
    have lowerFrame (address : Nat) (fromProof : proofBase ≤ address) (beforeCap : address < dest) :
        after.getByte (BitVec.ofNat 64 address) = lower.getByte (BitVec.ofNat 64 address) := by
      have byteFit : address < MEMORY_BYTES := by omega
      have safe : MEMORY_BYTES < 2^64 := by decide
      have heapBefore : trapdoorBase ≤ proofBase := by decide
      have prepStable := byte_memory lower prepared address byteFit
        (fun query low fit => cap_preparation_frame lower query low fit atCap.marks)
        (heapBefore.trans fromProof)
      exact (footerBytes.frame address (by omega) (Or.inl beforeCap)).trans prepStable
    let result : Execution := ⟨.success, final, openingCycles positions, 0⟩
    refine ⟨result, ?_, ⟨rfl, ?_, rfl, rfl, ⟨after, ?_, ?_, ?_⟩⟩⟩
    · change execute (s.image .opening) (s.steps .opening) initial true = pure result
      let surplus := s.steps .opening - openingSteps positions
      rw [abi.image, show s.steps .opening = 13+(590*positions.card-1)+770+capSubtreeCycles grouped 1 8 +
          (4 + Pack.exitSteps positions.card nodes.length + surplus) by omega,
        prefixTrace, ranExit]
      simp only [pure_bind, Execution.charge, result, cyclesEq]
    · change (final.getReg .x11).toNat = _
      rw [retLen]
      simp only [packedProofLength, frontier]
    · intro ordinal present _
      obtain ⟨nonce, siblings⟩ := written ordinal present present
      constructor
      · intro byte inside
        have prefixTrace : recordBase ordinal+byte < dest := by unfold dest recordBase recordBytes; omega
        exact (lowerFrame _ (by unfold recordBase; omega) prefixTrace).trans (nonce byte inside)
      · intro level levelBound byte inside
        have prefixTrace : siblingDestination ordinal level+byte < dest := by
          have reached := destination_mono ordinal (show level+1 ≤ 16 by omega)
          rw [record_end] at reached
          have step : siblingDestination ordinal (level+1) =
              siblingDestination ordinal level+siblingWidth level := by
            simp only [siblingDestination, sibling_offset_next, Nat.add_assoc]
          unfold dest recordBase recordBytes at *
          omega
        exact (lowerFrame _ (by unfold siblingDestination recordBase; omega) prefixTrace).trans
          (siblings level levelBound byte inside)
    · intro i inside
      have insideNodes : i < nodes.length := frontier ▸ inside
      let node := nodes[i]'insideNodes
      have nodeEq : (openingNodes positions)[i] = node := by
        have found := congrArg (fun l : List Nat => l[i]?) frontier
        rw [List.getElem?_eq_getElem inside, List.getElem?_eq_getElem insideNodes] at found
        exact Option.some.inj found
      rw [nodeEq]
      have small : node < 512 := Opening.cap_frontier_nodes_small grouped 1 8 Opening.cap_span_root
        node (List.getElem_mem insideNodes)
      have stable : readBuffer prepared (capDigestAddress node) 32 =
          readBuffer initial (capDigestAddress node) 32 := by
        have ⟨aligned, beforeProof⟩ := Opening.cap_digest_bounds node small
        apply Opening.copied_buffer _ _ _ _ 4 aligned aligned (by decide)
        intro j low
        have aboveHeap : trapdoorBase ≤ capDigestAddress node+8*j := by unfold capDigestAddress; omega
        have belowProof : capDigestAddress node+8*j < proofBase := by omega
        have fit : proofBase < 2^64 := by decide
        exact (cap_preparation_frame lower _ aboveHeap (by omega) atCap.marks).trans
          (atCap.input _ aboveHeap belowProof)
      have digest : readBuffer initial (capDigestAddress node) 32 =
          trapdoor.extractLsb' (256*node) 256 :=
        Opening.input_digest s abi.toOpeningLayout trapdoor positions node
          (small.trans_le (by decide : 512 ≤ 2*LENGTH))
      have written := footerBytes.digest i insideNodes
      rw [stable, digest] at written
      exact written
    · intro p inside
      have hL : proofLength positions = 498*positions.card + 30*nodes.length := by
        simp only [proofLength, frontier, recordBytes]
      rw [hL]
      exact packedBytes p (by simpa only [packedProofLength, frontier] using inside)

theorem opening_success (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (result : Execution) (physical : OpenPhysical s trapdoor positions result) :
    s.openingSucceeded result = true := by
  have bytes : (result.state.getReg .x11).toNat ≤ s.sizes.proof := by
    rw [physical.length]
    exact ((packed_proof_le positions).trans (proof_fits_every_cardinality positions)).trans abi.capacity
  simp [Submission.openingSucceeded, physical.success, bytes]

/-- Scored batch: the packer adds at most `Pack.exitCycles 128 128 - 4 = 2865069` cycles to the
unpacked opener's 85511, and the packed proof has at most 67072 bytes. -/
theorem opening_scored_limits (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (result : Execution) (physical : OpenPhysical s trapdoor positions result)
    (count : positions.card = BATCH) :
    result.cycles ≤ 2950580 ∧ (result.state.getReg .x11).toNat ≤ 67072 := by
  rw [physical.cycles, physical.length]
  have size : positions.card = 128 := count
  have nodes := Opening.opening_nodes_bound positions
  have old := (scheduled_scored_limits positions count).1
  have exit := Pack.exit_cycles_le positions.card _ (by omega) nodes
  constructor
  · unfold openingCycles; omega
  · unfold packedProofLength
    exact ProofCodec.packed_length_le _ _ (by omega) nodes

end TwoPermutationPrototype.PackedOpening
