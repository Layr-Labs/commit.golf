import CommitGolfCandidate.Layout2Run
import CommitGolfCandidate.GroupOpenFinish
import CommitGolfCandidate.QuartetOpeningSchedule
import CommitGolfCandidate.GroupOpenCopy

/-! Layout 2 opener after the pass: the record loop (`records_run`), the 770-cycle cap preparation, the chunked
cap walk (`capWalkB`) with the root exit `jal`, and the four-cycle return block. The result (`L2OpenPhysical`)
holds the Layout 2 record blocks, the flush bytes and the unchanged cap footer at `recordBase k`. -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate Sampling
open CommitGolfCandidate.Layout2Phase (stride PhaseFacts writerByte)
open QuartetOpening (proofLength)
open Opening (groupsBefore openingNodes capDigestAddress)
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

/-- Opening cycles after the 30-cycle header and the pass, with the same `+15` convention as today's
`wideCycles`: the record loop, the cap preparation, the cap walk with the root `jal`, and the return block. -/
def l2WideCycles (positions : Positions) : Nat :=
  if positions.card=0 then 7 else
    15+l2RecordsCost positions.card+769+
      (capWalkB (groupsBefore positions positions.card) 1 5 (recordBase positions.card) 0+2)+4

/-- Today's `OpeningABI`, restated here (the old record writer modules are not imported). -/
structure L2ABI (s : Submission) extends OpeningLayout s where
  image : s.image .opening = openingImage
  capacity : capacity ≤ s.sizes.proof
  fuel : 17179934720 ≤ s.steps .opening

/-- The opener's result: success, length, no oracle call, exact cycles, the Layout 2 record blocks and flush
bytes, and the cap footer. -/
structure L2OpenPhysical (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (result : Execution) : Prop where
  success : result.exit = .success
  length : (result.state.getReg .x11).toNat = proofLength positions
  noCalls : result.oracleCalls = 0
  cycles : result.cycles = l2WideCycles positions
  lower : L2Bytes (s.initialState .opening (trapdoor, positions)) positions result.state positions.card
  flush : ∀ b<flushLen ((positions.card+3)%4), result.state.getByte (BitVec.ofNat 64 (destOf positions.card+b))=
    (carryAt (s.initialState .opening (trapdoor, positions)) positions positions.card).extractLsb' (8*b) 8
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

theorem l2_wide_cycles_batch (positions : Positions) (count : positions.card = BATCH)
    (nodes : (capFrontierNodes (groupsBefore positions positions.card) 1 8).length ≤ 128) :
    l2WideCycles positions ≤ 15+30820+769+6130+6 := by
  have k : positions.card = 128 := count
  have aligned : (recordBase positions.card)%2=0 := by
    have : proofBase%2=0 := by decide
    unfold recordBase recordBytes; omega
  have cap := cap_walk_b_scored_bound (groupsBefore positions positions.card) (recordBase positions.card) aligned nodes
  rw [k] at cap
  unfold l2WideCycles
  rw [if_neg (by omega), k, records_cost_batch]
  omega

attribute [local irreducible] execute capPreparation readBuffer

/-- The record loop and the cap walk from the state at word 15. -/
theorem l2_body (phases : ∀ p<4, PhaseFacts openingImage p) (s : Submission) (abi : L2ABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) (begin : MachineState)
    (positive : 0<positions.card) (ready : L2Start s trapdoor positions begin) (surplus : Nat) :
    ∃ final, execute openingImage (l2WideCycles positions-15+surplus) begin true =
        pure ⟨.success,final,l2WideCycles positions-15,0⟩ ∧
      L2OpenPhysical s trapdoor positions ⟨.success,final,l2WideCycles positions,0⟩ := by
  let initial := s.initialState .opening (trapdoor, positions)
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have allFit := (Nat.add_le_add_left (QuartetOpening.capacity_all positions) _).trans packed_proof_memory
  have empty : positions.card ≠ 0 := Nat.ne_of_gt positive
  let grouped := groupsBefore positions positions.card
  let nodes := capFrontierNodes grouped 1 8
  let dest := recordBase positions.card
  obtain ⟨lower, ranRecords, done⟩ := records_run phases s abi.toOpeningLayout trapdoor positions begin positive ready
  let prepared := capPreparation lower
  have leafMarks (node : Nat) (leaf : 255 < node) (inside : node < 512) :
      Opening.machineMarks lower node = Opening.markWord grouped node := by
    rw [done.marked node inside, Opening.mark_word_leaf grouped ⟨node,inside⟩ (show 256 ≤ node by omega)]
  have destReg : lower.getReg .x21 = BitVec.ofNat 64 dest := by rw [done.dest]; rfl
  have ⟨rootPC, root, countdown⟩ := cap_preparation_context lower grouped dest
    done.marks done.capHeap done.capLeaves done.proofBegin done.one destReg leafMarks
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
  let capCost := capWalkB grouped 1 5 dest 0
  let recCost := l2RecordsCost positions.card
  have charge : l2WideCycles positions = 15+recCost+770+capCost+5 := by
    rw [l2WideCycles, if_neg empty]
    dsimp only [grouped, capCost, recCost, dest]
    omega
  have ranPrep : RunsOpeningBlock lower prepared 770 :=
    execute_cap_preparation lower (by rw [done.pc]; rfl) done.marks
  have ⟨ranExit, finalMem, retLen⟩ := root_exit after afterPC surplus true
  have lowerFrame (address : Nat) (fromProof : proofBase ≤ address) (beforeCap : address < dest) :
      final.getByte (BitVec.ofNat 64 address) = lower.getByte (BitVec.ofNat 64 address) := by
    have byteFit : address < MEMORY_BYTES := by omega
    have safe : MEMORY_BYTES < 2^64 := by decide
    have heapBefore : trapdoorBase ≤ proofBase := by decide
    have prepStable := byte_memory lower prepared address byteFit
      (fun query low fit => cap_preparation_frame lower query low fit done.marks)
      (heapBefore.trans fromProof)
    have unchanged := (footerFrame address (by omega) (Or.inl beforeCap)).trans prepStable
    have eq : final.mem = after.mem := finalMem
    simpa only [MachineState.getByte, MachineState.getMem, eq] using unchanged
  have flushEnd := dest_flush positions.card positive
  have destEq : dest = proofBase+534*positions.card := rfl
  refine ⟨final,?_,⟨rfl,?_,rfl,rfl,?_,?_,?_⟩⟩
  · rw [show l2WideCycles positions-15+surplus=recCost+770+(capCost+1)+(4+surplus) by omega]
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
  · intro j hj b hb
    have mono := dest_mono j positions.card hj
    have lo := (dest_bound j).1
    rw [lowerFrame _ (by omega) (by omega)]
    exact done.bytes j hj b hb
  · intro b hb
    have lo := (dest_bound positions.card).1
    change final.getByte _ = _
    rw [lowerFrame _ (by omega) (by omega)]
    exact done.flush b hb
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
        exact (cap_preparation_frame lower _ aboveHeap (by omega) done.marks).trans
          (done.input _ aboveHeap belowProof a)
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

end TwoPermutationPrototype.GroupedOpening.Layout2
