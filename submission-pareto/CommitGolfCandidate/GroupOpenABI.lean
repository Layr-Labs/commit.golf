import CommitGolfCandidate.GroupOpenInitial
import CommitGolfCandidate.GroupOpenFinish
import CommitGolfCandidate.QuartetOpeningSchedule

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp Sampling
open QuartetOpening (proofLength)
open Opening (groupsBefore openingNodes capDigestAddress)

/-- Wide record copies, 771-cycle cap preparation, the cap walk (three-cycle steps across, four-cycle climbs),
the one-cycle root exit `jal` and the four-cycle return block. -/
def wideCycles (positions : Positions) : Nat :=
  if positions.card = 0 then 7 else
    15 + (134*positions.card+copySum positions.card+1) + 770 +
      (capWalkCycles (Opening.groupsBefore positions positions.card) 1 8 (recordBase positions.card) 0+2) + 4

theorem copy_sum_le (n : Nat) : copySum n ≤ 517*n := by
  induction n with
  | zero => rfl
  | succ n ih => have := record_extra_le n; simp only [copySum]; omega

theorem copy_sum_batch : copySum 128 = 49184 := by decide +kernel

theorem wide_cycles_le_old (positions : Positions) :
    wideCycles positions+536*positions.card+(if positions.card = 0 then 0 else 1785) ≤ QuartetOpening.scheduledCycles positions+copySum positions.card := by
  have cap := cap_cycles_le_old (Opening.groupsBefore positions positions.card) 1 8
  have saving := cap_walk_le_old (Opening.groupsBefore positions positions.card) 1 8 (recordBase positions.card)
  unfold wideCycles QuartetOpening.scheduledCycles
  by_cases empty : positions.card = 0
  · simp only [empty]; exact Nat.le_refl _
  · simp only [ite_eq_right empty]
    have nodes : (Opening.openingNodes positions).length=
        (capFrontierNodes (Opening.groupsBefore positions positions.card) 1 8).length := by
      simp [Opening.openingNodes, empty]
    omega

theorem wide_cycles_le (p : Positions) (nz : p.card ≠ 0) : wideCycles p ≤ 15+688*p.card+98216 := by
  have h := QuartetOpening.scheduled_cycles_le p nz
  have e := wide_cycles_le_old p
  rw [ite_eq_right nz] at e
  have c := copy_sum_le p.card
  omega

theorem wide_scored_limits (positions : Positions) (count : positions.card = BATCH) :
    wideCycles positions ≤ 76202 ∧ proofLength positions ≤ 72160 := by
  have old := QuartetOpening.scored_limits positions count
  have nodes := Opening.opening_nodes_bound positions
  have k : positions.card = 128 := count
  have frontier : Opening.openingNodes positions=capFrontierNodes (Opening.groupsBefore positions positions.card) 1 8 := by
    unfold Opening.openingNodes
    rw [if_neg (by omega)]
  rw [frontier] at nodes
  have aligned : (recordBase positions.card)%2=0 := by
    unfold recordBase recordBytes
    have : proofBase%2=0 := by decide
    omega
  have cap := cap_walk_scored_bound (Opening.groupsBefore positions positions.card) (recordBase positions.card) aligned nodes
  rw [k] at cap
  have c : copySum positions.card = 49184 := by rw [k, copy_sum_batch]
  refine ⟨?_, old.2⟩
  unfold wideCycles
  rw [if_neg (by omega), c, k]
  omega

structure OpeningABI (s : Submission) extends OpeningLayout s where
  image : s.image .opening = openingImage
  capacity : capacity ≤ s.sizes.proof
  fuel : 17179934720 ≤ s.steps .opening

structure OpenPhysical (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (result : Execution) : Prop where
  success : result.exit = .success
  length : (result.state.getReg .x11).toNat = proofLength positions
  noCalls : result.oracleCalls = 0
  cycles : result.cycles = wideCycles positions
  lower : CompletedRecords s trapdoor positions result.state positions.card
  footer : bytesAt result.state (recordBase positions.card) (capOffset (openingNodes positions).length) =
    foldNodes ((openingNodes positions).map (fun n => trapdoor.extractLsb' (256*n) 256))

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

/-- With at least one opened position the cap root is marked (every cap group lies in `[256, 512)`). -/
theorem cap_root_marked (positions : Positions) (positive : 0 < positions.card) :
    capIsMarked (groupsBefore positions positions.card) 1 8 = true := by
  have size : (groupsBefore positions positions.card).length = positions.card := by
    simp [groupsBefore]
  cases hg : groupsBefore positions positions.card with
  | nil => rw [hg] at size; simp at size; omega
  | cons g rest =>
    have member : g ∈ groupsBefore positions positions.card := by rw [hg]; simp
    unfold groupsBefore at member
    obtain ⟨index, _, value⟩ := List.mem_map.1 member
    have bound : index.val < 16777216 := index.isLt
    have high : g / 2^8 = 1 := by
      rw [← value]
      change (16777216+index.val)/65536/256 = 1
      omega
    simp only [capIsMarked, List.any_eq_true, beq_iff_eq]
    exact ⟨g, by simp, high⟩

attribute [local irreducible] execute capPreparation setupPrefix readBuffer

/-- The original record writer and cap walk from a materialized virtual trapdoor. -/
theorem body_from_boundary (recordsExecute : RecordsExecute) (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (begin : MachineState) (positive : 0<positions.card)
    (ready : RecordBoundary s trapdoor positions begin 0) (marks : Opening.RecordMarks positions begin 0)
    (surplus : Nat) :
    ∃ final, execute openingImage (wideCycles positions-15+surplus) begin true =
        pure ⟨.success,final,wideCycles positions-15,0⟩ ∧
      OpenPhysical s trapdoor positions ⟨.success,final,wideCycles positions,0⟩ := by
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
    have ⟨rootPC, root, countdown⟩ := cap_preparation_context lower grouped dest
      atCap.marks atCap.capHeap atCap.capLeaves atCap.proofBegin atCap.one atCap.dest leafMarks
    have frontier : openingNodes positions = nodes := by simp [openingNodes, empty, nodes, grouped]
    have lengthSplit : proofLength positions = 534*positions.card+capOffset nodes.length := by
      unfold proofLength capOffset
      rw [frontier]
      omega
    have spare : proofLength positions+2 ≤ capacity := by
      have nodeCount := Opening.opening_nodes_bound positions
      have c : positions.card ≤ LENGTH := cardinal
      unfold proofLength capacity recordBytes
      generalize LENGTH = L at c ⊢
      generalize (openingNodes positions).length = f at nodeCount ⊢
      omega
    have room : dest+capOffset nodes.length+2 ≤ MEMORY_BYTES := by
      have memory : proofBase+capacity ≤ MEMORY_BYTES := packed_proof_memory
      have eq : dest+capOffset nodes.length+2 = proofBase+(proofLength positions+2) := by
        rw [lengthSplit]
        unfold dest recordBase recordBytes
        omega
      rw [eq]
      exact (Nat.add_le_add_left spare _).trans memory
    have aligned : dest % 2 = 0 := by
      have base : proofBase % 2 = 0 := by decide
      unfold dest recordBase recordBytes
      omega
    have above : proofBase ≤ dest := by unfold dest recordBase; omega
    obtain ⟨after, ranCap, afterPC, endPosition, footerFrame, footerBytes⟩ :=
      cap_root grouped prepared dest root (cap_root_marked positions positive) rootPC
        ((show Opening.proofBase≤proofBase by decide).trans above) aligned room countdown
    let final := exitPrefix after 3
    let capCost := capWalkCycles grouped 1 8 dest 0
    let recCost := 134*positions.card+copySum positions.card+1
    have charge : wideCycles positions = 15+recCost+771+capCost+5 := by
      rw [wideCycles, if_neg empty]
      dsimp only [grouped, capCost, recCost, dest]
      omega
    have ranRecords : RunsOpeningBlock begin lower recCost := by
      have charged : recordsCost positions.card 0 positions.card = recCost := records_total _ positive
      exact charged ▸ assembled.run
    have ranPrep : RunsOpeningBlock lower prepared 771 :=
      execute_cap_preparation lower (by simpa using atCap.pc) atCap.marks
    have ⟨ranExit, finalMem, retLen⟩ := root_exit after afterPC surplus true
    have lowerFrame (address : Nat) (fromProof : proofBase ≤ address) (beforeCap : address < dest) :
        final.getByte (BitVec.ofNat 64 address) = lower.getByte (BitVec.ofNat 64 address) := by
      have byteFit : address < MEMORY_BYTES := by omega
      have safe : MEMORY_BYTES < 2^64 := by decide
      have heapBefore : trapdoorBase ≤ proofBase := by decide
      have prepStable := byte_memory lower prepared address byteFit
        (fun query low fit => cap_preparation_frame lower query low fit atCap.marks)
        (heapBefore.trans fromProof)
      have unchanged := (footerFrame address (by omega) (Or.inl beforeCap)).trans prepStable
      have eq : final.mem = after.mem := finalMem
      simpa only [MachineState.getByte, MachineState.getMem, eq] using unchanged
    refine ⟨final,?_,⟨rfl,?_,rfl,rfl,?_,?_⟩⟩
    · have nl : nodes.length = (Sampling.capFrontierNodes grouped 1 8).length := rfl
      rw [show wideCycles positions-15+surplus=
          recCost+771+(capCost+1)+(4+surplus) by omega]
      rw [((ranRecords.next ranPrep).next ranCap) (4+surplus) true,ranExit]
      simp [Execution.charge,final]
      omega
    · change (final.getReg .x11).toNat = _
      have ret : final.getReg .x11 = after.getReg .x21-after.getReg .x20 := retLen
      rw [ret]
      apply terminal_length after _ _ endPosition.context.proofStart allFit
      have destination := endPosition.destWord
      rw [lengthSplit]
      simpa only [dest, recordBase, recordBytes, actual_proof_base, Nat.add_assoc] using destination
    · intro ordinal present _
      obtain ⟨nonce, siblings, folds⟩ := written ordinal present present
      have recordEnd : recordBase (ordinal+1) ≤ dest := by
        unfold dest recordBase recordBytes
        have : ordinal+1 ≤ positions.card := present
        omega
      have levelEnd (level : Nat) (inside : level < 14) :
          siblingDestination ordinal level+siblingWidth level ≤ dest := by
        have reached := destination_mono ordinal (show level+1 ≤ 14 by omega)
        rw [record_end] at reached
        have step : siblingDestination ordinal (level+1) =
            siblingDestination ordinal level+siblingWidth level := by
          simp only [siblingDestination, sibling_offset_next level inside, Nat.add_assoc]
        omega
      refine ⟨?_, ?_, ?_⟩
      · intro byte inside
        have prefixTrace : recordBase ordinal+byte < dest := by
          have : recordBase ordinal+112 ≤ recordBase (ordinal+1) := by unfold recordBase recordBytes; omega
          omega
        exact (lowerFrame _ (by unfold recordBase; omega) prefixTrace).trans (nonce byte inside)
      · intro level levelBound byte inside
        have narrow := plain_width_le level
        have prefixTrace : siblingDestination ordinal level+byte < dest := by
          have := levelEnd level levelBound
          omega
        exact (lowerFrame _ (by unfold siblingDestination recordBase; omega) prefixTrace).trans
          (siblings level levelBound byte inside)
      · intro k small b two
        have wide : siblingWidth (6+k) = 30 := by unfold siblingWidth; split <;> (try split) <;> omega
        have prefixTrace : siblingDestination ordinal (6+k)+28+b < dest := by
          have := levelEnd (6+k) (by omega)
          omega
        exact (lowerFrame _ (by unfold siblingDestination recordBase; omega) prefixTrace).trans
          (folds k small b two)
    · have returnMem : final.mem = after.mem := finalMem
      have stable (node : Nat) (member : node ∈ nodes) :
          readBuffer prepared (capDigestAddress node) 32 = Opening.trapdoorHeap (s:=s) trapdoor node := by
        have small : node < 512 := Opening.cap_frontier_nodes_small grouped 1 8 Opening.cap_span_root node member
        have kept : readBuffer prepared (capDigestAddress node) 32 =
            readBuffer initial (capDigestAddress node) 32 := by
          have ⟨aligned, beforeProof⟩ := Opening.cap_digest_bounds node small
          apply Opening.copied_buffer _ _ _ _ 4 aligned aligned (by decide)
          intro j low
          have aboveHeap : trapdoorBase ≤ capDigestAddress node+8*j := by
            change trapdoorBase ≤ trapdoorBase+32*node+8*j; omega
          have belowProof : capDigestAddress node+8*j < proofBase := by
            have old : Opening.proofBase ≤ proofBase := by decide
            omega
          have fit : proofBase < 2^64 := by decide
          have a : (capDigestAddress node+8*j)%8=0 := by omega
          exact (cap_preparation_frame lower _ aboveHeap (by omega) atCap.marks).trans
            (atCap.input _ aboveHeap belowProof a)
        rw [kept]
        exact input_digest s abi.toOpeningLayout trapdoor positions node
          (small.trans_le (by decide : 512 ≤ 2*LENGTH))
      have values : nodes.map (fun n => readBuffer prepared (capDigestAddress n) 32) =
          nodes.map (Opening.trapdoorHeap (s:=s) trapdoor) := List.map_congr_left stable
      have finalBytes : bytesAt final dest (capOffset nodes.length) = bytesAt after dest (capOffset nodes.length) := by
        simp only [bytesAt, MachineState.getByte, MachineState.getMem, returnMem]
      change bytesAt final dest (capOffset (openingNodes positions).length) =
        foldNodes ((openingNodes positions).map (fun n => trapdoor.extractLsb' (256*n) 256))
      rw [frontier, finalBytes, footerBytes, values]
      rfl

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
    result.cycles ≤ 76202 ∧ (result.state.getReg .x11).toNat ≤ 72160 := by
  rw [physical.cycles, physical.length]
  exact wide_scored_limits positions count

end TwoPermutationPrototype.GroupedOpening
