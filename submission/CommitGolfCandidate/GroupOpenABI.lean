import CommitGolfCandidate.GroupOpenInitial
import CommitGolfCandidate.GroupOpenFinish

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp Sampling
open PackedOpening (capSubtreeCycles)
open QuartetOpening (proofLength scheduledCycles)
open Opening (groupsBefore openingNodes capDigestAddress)

structure OpeningABI (s : Submission) extends OpeningLayout s where
  image : s.image .opening = openingImage
  capacity : capacity ≤ s.sizes.proof
  fuel : 17179934720 ≤ s.steps .opening

structure OpenPhysical (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (result : Execution) : Prop where
  success : result.exit = .success
  length : (result.state.getReg .x11).toNat = proofLength positions
  noCalls : result.oracleCalls = 0
  cycles : result.cycles = scheduledCycles positions
  lower : CompletedRecords s trapdoor positions result.state positions.card
  footer : ∀ i (inside : i < (openingNodes positions).length),
    readBuffer result.state (recordBase positions.card+30*i) 30 =
      (trapdoor.extractLsb' (256*(openingNodes positions)[i]) 256).extractLsb' 0 240

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

/-- The original record writer and cap walk from a materialized virtual trapdoor. -/
theorem body_from_boundary (recordsExecute : RecordsExecute) (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (begin : MachineState) (positive : 0<positions.card)
    (ready : RecordBoundary s trapdoor positions begin 0) (marks : Opening.RecordMarks positions begin 0)
    (surplus : Nat) :
    ∃ final, execute openingImage (scheduledCycles positions-15+surplus) begin true =
        pure ⟨.success,final,scheduledCycles positions-15,0⟩ ∧
      OpenPhysical s trapdoor positions ⟨.success,final,scheduledCycles positions,0⟩ := by
    let initial := s.initialState .opening (trapdoor, positions)
    have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
    have allFit := (Nat.add_le_add_left (QuartetOpening.capacity_all positions) _).trans packed_proof_memory
    have empty : positions.card ≠ 0 := Nat.ne_of_gt positive
    let grouped := groupsBefore positions positions.card
    let nodes := capFrontierNodes grouped 1 8
    let dest := recordBase positions.card
    let lower := runRecords positions.card 0 positions.card begin
    let prepared := capPreparation lower
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
      simpa only [proofLength, frontier, dest, recordBase, recordBytes, Nat.add_assoc] using allFit
    have aligned : dest % 2 = 0 := by
      have base : proofBase % 2 = 0 := by decide
      unfold dest recordBase recordBytes
      omega
    have above : proofBase ≤ dest := by unfold dest recordBase; omega
    obtain ⟨after, ranCap, afterPC, endPosition, footerBytes⟩ :=
      cap_subtree grouped prepared 1 8 dest Opening.cap_span_root root rootPC ((show Opening.proofBase≤proofBase by decide).trans above) aligned room
    let final := exitPrefix (advancePrefix after 41 2) 3
    have charge : scheduledCycles positions = 15+(634*positions.card-1)+2552+capSubtreeCycles grouped 1 8+6 := by
      rw [scheduledCycles, if_neg empty]
      dsimp only [grouped]
      omega
    have ranRecords : RunsOpeningBlock begin lower (634*positions.card-1) := by
      have charged : recordsCost positions.card 0 positions.card = 634*positions.card-1 := by
        simp [recordsCost, positive]
      exact charged ▸ assembled.run
    have ranPrep : RunsOpeningBlock lower prepared 2552 :=
      execute_cap_preparation lower (by simpa using atCap.pc) atCap.marks
    have ⟨ranExit, finalMem, retLen⟩ := root_exit after afterPC endPosition.nodeWord surplus true
    have lowerFrame (address : Nat) (fromProof : proofBase ≤ address) (beforeCap : address < dest) :
        final.getByte (BitVec.ofNat 64 address) = lower.getByte (BitVec.ofNat 64 address) := by
      have byteFit : address < MEMORY_BYTES := by omega
      have safe : MEMORY_BYTES < 2^64 := by decide
      have heapBefore : trapdoorBase ≤ proofBase := by decide
      have prepStable := byte_memory lower prepared address byteFit
        (fun query low fit => cap_preparation_frame lower query low fit atCap.marks)
        (heapBefore.trans fromProof)
      have unchanged := (footerBytes.frame address (by omega) (Or.inl beforeCap)).trans prepStable
      have eq : final.mem = after.mem := finalMem
      simpa only [MachineState.getByte, MachineState.getMem, eq] using unchanged
    refine ⟨final,?_,⟨rfl,?_,rfl,rfl,?_,?_⟩⟩
    · rw [show scheduledCycles positions-15+surplus=
          (634*positions.card-1)+2552+capSubtreeCycles grouped 1 8+(6+surplus) by omega]
      rw [((ranRecords.next ranPrep).next ranCap) (6+surplus) true,ranExit]
      simp [Execution.charge,final]
      omega
    · change (final.getReg .x11).toNat = _
      have ret : final.getReg .x11 = after.getReg .x21-after.getReg .x20 := retLen
      rw [ret]
      apply terminal_length after _ _ endPosition.context.proofStart allFit
      simpa only [proofLength, frontier, dest, recordBase, recordBytes, actual_proof_base, nodes, Nat.add_assoc] using endPosition.destWord
    · intro ordinal present _
      obtain ⟨nonce, siblings⟩ := written ordinal present present
      constructor
      · intro byte inside
        have prefixTrace : recordBase ordinal+byte < dest := by unfold dest recordBase recordBytes; omega
        exact (lowerFrame _ (by unfold recordBase; omega) prefixTrace).trans (nonce byte inside)
      · intro level levelBound byte inside
        have prefixTrace : siblingDestination ordinal level+byte < dest := by
          have reached := destination_mono ordinal (show level+1 ≤ 14 by omega)
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
        have aboveHeap : trapdoorBase ≤ capDigestAddress node+8*j := by change trapdoorBase ≤ trapdoorBase+32*node+8*j; omega
        have belowProof : capDigestAddress node+8*j < proofBase := by
          have old : Opening.proofBase ≤ proofBase := by decide
          omega
        have fit : proofBase < 2^64 := by decide
        have a : (capDigestAddress node+8*j)%8=0 := by omega
        exact (cap_preparation_frame lower _ aboveHeap (by omega) atCap.marks).trans
          (atCap.input _ aboveHeap belowProof a)
      have digest : readBuffer initial (capDigestAddress node) 32 =
          trapdoor.extractLsb' (256*node) 256 :=
        input_digest s abi.toOpeningLayout trapdoor positions node
          (small.trans_le (by decide : 512 ≤ 2*LENGTH))
      have written := footerBytes.digest i insideNodes
      rw [stable, digest] at written
      have returnMem : final.mem = after.mem := finalMem
      change readBuffer final (dest+30*i) 30 = _
      have saved : readBuffer final (dest+30*i) 30 = readBuffer after (dest+30*i) 30 := by
        simp only [readBuffer, MachineState.getByte, MachineState.getMem, returnMem]
      exact saved.trans written

theorem opening_success (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (result : Execution) (physical : OpenPhysical s trapdoor positions result) :
    s.openingSucceeded result = true := by
  have bytes : (result.state.getReg .x11).toNat ≤ s.sizes.proof := by
    rw [physical.length]
    exact (QuartetOpening.capacity_all positions).trans abi.capacity
  simp [Submission.openingSucceeded, physical.success, bytes]

theorem opening_scored_limits (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (result : Execution) (physical : OpenPhysical s trapdoor positions result)
    (count : positions.card = BATCH) :
    result.cycles ≤ 93945 ∧ (result.state.getReg .x11).toNat ≤ 72192 := by
  rw [physical.cycles, physical.length]
  exact QuartetOpening.scored_limits positions count

end TwoPermutationPrototype.GroupedOpening
