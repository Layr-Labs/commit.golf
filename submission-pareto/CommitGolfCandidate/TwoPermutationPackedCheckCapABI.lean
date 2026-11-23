import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.TwoPermutationPackedCheckerBody
import CommitGolfCandidate.TwoPermutationPackedCapComplete
import CommitGolfCandidate.K3C4CapHonest
import CommitGolfCandidate.TwoPermutationPackedFrontierCount

/-! # The checker's cap phase from the record cursor (T238)

After the last 534-byte record the honest proof carries the packed cap frontier
`Quartet.frontierProof238`: full groups of eight 238-bit nodes in 238 bytes, a trailing partial group
in 30-byte slots, `capPackedBytes f` bytes for `f` frontier nodes. This file builds `CapSuffixReady`
from the record cursor, decodes the honest frontier through `cap_frontier_of_pack`, and closes C2's
`CheckerCapFacts` at cap fuel 40000. -/

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (RecordInputFrame capRootAt checker_positions_bound record_input_root
  checker_honest_cap_nodes record_groups_length checkSourceWord)
open TwoPermutationPrototype.QuartetCertificate (honestCheckInput)
set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

private theorem frontier_node_bounds (groups : List Nat) (node height : Nat)
    (span : Opening.CapSpan node height) (entry : Nat)
    (member : entry ∈ capFrontierNodes groups node height) : 0 < entry ∧ entry < 512 := by
  induction height generalizing node with
  | zero =>
    unfold capFrontierNodes at member
    split at member
    · simp at member
    · rw [List.mem_singleton] at member
      subst entry
      exact Opening.cap_span_node _ _ span
  | succ height ih =>
    unfold capFrontierNodes at member
    split at member
    · obtain ⟨left,right⟩ := Opening.cap_span_children node height span
      rcases List.mem_append.mp member with child | child
      · exact ih _ left child
      · exact ih _ right child
    · rw [List.mem_singleton] at member
      subst entry
      exact Opening.cap_span_node _ _ span

private theorem checker_cap_frontier_bound (input : CheckInput) :
    (capFrontierNodes (Opening.groupsBefore input.positions input.positions.card) 1 8).length ≤ 128 := by
  rw [cap_frontier_length]
  exact production_boundary_bound _

theorem checker_cap_ready (oracle : Oracle) (input : CheckInput) (state : MachineState) (rows : List PublicRow)
    (cursor : RecordCursor input input.positions.card state)
    (table : CollectedTable oracle input input.positions.card state rows) :
    CapSuffixReady (Opening.groupsBefore input.positions input.positions.card) state
      (checkProofByte input.positions.card) 536871424 := by
  refine ⟨cursor.pc.trans (ite_eq_left rfl),
    cursor.proof,cursor.capRoots,cursor.marks,cursor.capCount,cursor.selector,cursor.commitment,?_ ,
    ?_,?_ ,?_ ,by decide,by decide⟩
  · intro node low high
    exact (table.marks node high).trans (Opening.mark_word_leaf _ ⟨node,high⟩ low).symm
  · unfold checkProofByte
    omega
  · unfold checkProofByte
    omega
  · have card := checker_positions_bound input
    have frontier := checker_cap_frontier_bound input
    have packed := cap_packed_bytes_le
      (capFrontierNodes (Opening.groupsBefore input.positions input.positions.card) 1 8).length
    unfold MEMORY_BYTES checkProofByte
    omega

/-- The bytes of an honest input's packed frontier, read where the checker left them after the records. -/
private theorem honest_frontier_bytes (oracle : Oracle) (input : CheckInput) (state : MachineState)
    (framed : RecordInputFrame input input.positions.card state) (positive : input.positions.card ≠ 0)
    (message : Message) (salts : CompleteSaltTape)
    (canonical : input = honestCheckInput oracle message input.positions salts) :
    ∀ j < (Quartet.packNodes ((capFrontierNodes (Opening.groupsBefore input.positions input.positions.card) 1 8).map
        (PackedHonest.honestHeap oracle message salts))).length,
      state.getByte (BitVec.ofNat 64 (checkProofByte input.positions.card+j)) =
        (Quartet.packNodes ((capFrontierNodes (Opening.groupsBefore input.positions input.positions.card) 1 8).map
          (PackedHonest.honestHeap oracle message salts)))[j]! := by
  intro j inside
  have size : (Opening.groupsBefore input.positions input.positions.card).length = input.positions.card :=
    record_groups_length input _ (Nat.le_refl _)
  have occupied : (Opening.groupsBefore input.positions input.positions.card).isEmpty = false := by
    apply Bool.eq_false_of_not_eq_true
    rw [List.isEmpty_iff]
    intro nil
    exact positive (size.symm.trans (by rw [nil]; rfl))
  have frontier : Quartet.frontierProof238 (PackedHonest.honestHeap oracle message salts)
      (Opening.groupsBefore input.positions input.positions.card) =
      Quartet.packNodes ((capFrontierNodes (Opening.groupsBefore input.positions input.positions.card) 1 8).map
        (PackedHonest.honestHeap oracle message salts)) := by
    unfold Quartet.frontierProof238
    rw [ite_eq_right (by rw [occupied]; decide)]
  have whole := (congrArg CheckInput.proof canonical).trans
    (PackedHonest.honest_proof_parts oracle message input.positions salts)
  rw [frontier] at whole
  obtain ⟨records, parts, width⟩ : ∃ records : List Byte,
      input.proof = records ++ Quartet.packNodes ((capFrontierNodes (Opening.groupsBefore input.positions
        input.positions.card) 1 8).map (PackedHonest.honestHeap oracle message salts)) ∧
      records.length = 534*input.positions.card :=
    ⟨_, whole, by
      rw [PackedHonest.fixed_flatmap_length _ 534 (fun _ => Quartet.opening_record_length _ _ _ _) _,
        PackedHonest.honest_order_length]⟩
  have card := checker_positions_bound input
  have bound := checker_cap_frontier_bound input
  have packed := Quartet.pack_nodes_length ((capFrontierNodes (Opening.groupsBefore input.positions
    input.positions.card) 1 8).map (PackedHonest.honestHeap oracle message salts))
  rw [List.length_map] at packed
  have present : 534*input.positions.card+j < input.proof.length := by
    rw [parts, List.length_append, width]
    omega
  have valid : input.proof.length ≤ PackedChecker.submission.sizes.proof :=
    (Nat.le_of_eq (congrArg (fun value : CheckInput => value.proof.length) canonical)).trans
      (PackedHonest.honest_input_admitted oracle message input.positions salts)
  have address : PackedChecker.submission.layout.proof+(534*input.positions.card+j) =
      checkProofByte input.positions.card+j := by
    change 13824430176+(534*input.positions.card+j) = _
    unfold checkProofByte
    omega
  have loaded := PackedChecker.check_input_proof_byte input valid _ present
  rw [PackedChecker.initial_state, address] at loaded
  have kept : state.getByte (BitVec.ofNat 64 (checkProofByte input.positions.card+j)) =
      (QAssembly.submission.initialState .check input).getByte
        (BitVec.ofNat 64 (checkProofByte input.positions.card+j)) := by
    apply byte_frame
    apply framed _ (by unfold checkProofByte; omega)
    exact Or.inr (Or.inr (by unfold checkSourceWord checkProofByte; omega))
  have after : records.length ≤ 534*input.positions.card+j := by omega
  have entry : input.proof[534*input.positions.card+j]? =
      (Quartet.packNodes ((capFrontierNodes (Opening.groupsBefore input.positions input.positions.card) 1 8).map
        (PackedHonest.honestHeap oracle message salts)))[j]? := by
    rw [parts, List.getElem?_append_right after, width, Nat.add_sub_cancel_left]
  rw [List.getElem?_eq_getElem present, List.getElem?_eq_getElem inside] at entry
  rw [kept, loaded, Option.some_inj.mp entry, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem inside,
    Option.getD_some]

/-- The packed frontier bytes of any input whose proof is `records ++ packNodes nodes` with 534 k record bytes. -/
theorem packed_frontier_bytes (input : CheckInput) (state : MachineState)
    (framed : RecordInputFrame input input.positions.card state) (nodes : List (BitVec 256)) (records : List Byte)
    (parts : input.proof = records ++ Quartet.packNodes nodes) (width : records.length = 534*input.positions.card)
    (valid : input.proof.length ≤ PackedChecker.submission.sizes.proof) :
    ∀ j < (Quartet.packNodes nodes).length,
      state.getByte (BitVec.ofNat 64 (checkProofByte input.positions.card+j)) = (Quartet.packNodes nodes)[j]! := by
  intro j inside
  have card := checker_positions_bound input
  have present : 534*input.positions.card+j < input.proof.length := by
    rw [parts, List.length_append, width]
    omega
  have address : PackedChecker.submission.layout.proof+(534*input.positions.card+j) =
      checkProofByte input.positions.card+j := by
    change 13824430176+(534*input.positions.card+j) = _
    unfold checkProofByte
    omega
  have loaded := PackedChecker.check_input_proof_byte input valid _ present
  rw [PackedChecker.initial_state, address] at loaded
  have kept : state.getByte (BitVec.ofNat 64 (checkProofByte input.positions.card+j)) =
      (QAssembly.submission.initialState .check input).getByte
        (BitVec.ofNat 64 (checkProofByte input.positions.card+j)) := by
    apply byte_frame
    have small : input.proof.length ≤ 8959041024 := valid
    apply framed _ (by unfold checkProofByte; omega)
    exact Or.inr (Or.inr (by unfold checkSourceWord checkProofByte; omega))
  have after : records.length ≤ 534*input.positions.card+j := by omega
  have entry : input.proof[534*input.positions.card+j]? = (Quartet.packNodes nodes)[j]? := by
    rw [parts, List.getElem?_append_right after, width, Nat.add_sub_cancel_left]
  rw [List.getElem?_eq_getElem present, List.getElem?_eq_getElem inside] at entry
  rw [kept, loaded, Option.some_inj.mp entry, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem inside,
    Option.getD_some]

theorem checker_honest_cap_data (oracle : Oracle) (input : CheckInput) (state : MachineState)
    (rows : List PublicRow) (table : CollectedTable oracle input input.positions.card state rows)
    (framed : RecordInputFrame input input.positions.card state)
    (cursor : RecordCursor input input.positions.card state) (positive : input.positions.card ≠ 0)
    (message : Message) (salts : CompleteSaltTape)
    (canonical : input = honestCheckInput oracle message input.positions salts) :
    let groups := Opening.groupsBefore input.positions input.positions.card
    let pointer := checkProofByte input.positions.card
    let heap := PackedHonest.honestHeap oracle message salts
    CapContents groups state 1 8 pointer 0 heap ∧
      readBuffer state (8*536871424) 32 = heap 1 ∧
      state.getReg .x22 = BitVec.ofNat 64 (pointer+capPackedBytes (capFrontierNodes groups 1 8).length) := by
  intro groups pointer heap
  have nodes : Opening.openingNodes input.positions = capFrontierNodes groups 1 8 :=
    checker_honest_cap_nodes input.positions positive
  refine ⟨⟨?_,?_⟩,?_ ,?_⟩
  · intro leaf seen _ _ _
    exact table.honest message salts (NearHonest.of_eq canonical) leaf seen
  · intro i bounded
    have member := List.getElem_mem (l := capFrontierNodes groups 1 8) bounded
    obtain ⟨positiveNode, capNode⟩ := frontier_node_bounds groups 1 8 Opening.cap_span_root _ member
    have decoded := cap_frontier_of_pack state pointer ((capFrontierNodes groups 1 8).map heap)
      (honest_frontier_bytes oracle input state framed positive message salts canonical) i
      (by rw [List.length_map]; exact bounded)
    have entry : ((capFrontierNodes groups 1 8).map heap)[i]! = heap ((capFrontierNodes groups 1 8)[i]) := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem bounded]
      rfl
    rw [Nat.zero_add, decoded, entry]
    exact PackedHonest.honest_projected238_node oracle message salts _ positiveNode (by omega)
  · have root := record_input_root input input.positions.card state framed
    exact root.trans (congrArg CheckInput.commitment canonical)
  · rw [cursor.proofEnd]
    have proofLen := congrArg (fun value : CheckInput => value.proof.length) canonical
    change BitVec.ofNat 64 (13824430176+input.proof.length) =
      BitVec.ofNat 64 (pointer+capPackedBytes (capFrontierNodes groups 1 8).length)
    rw [proofLen, PackedHonest.honest_proof_length, nodes, cap_packed_bytes_closed]
    apply congrArg (BitVec.ofNat 64)
    dsimp only [pointer, checkProofByte]
    omega

theorem pick_unmarked {groups : List Nat} {u : Nat} (picked : groupPick groups = some u) (h : u ≠ 255) :
    capIsMarked groups u 0 = false := by
  unfold groupPick at picked
  by_cases a : capIsMarked groups 511 0 = false <;> by_cases b : capIsMarked groups 510 0 = false
  · rw [if_pos a, if_pos b] at picked; cases picked; exact absurd rfl h
  · rw [if_pos a, if_neg b] at picked; cases picked; exact a
  · rw [if_neg a, if_pos b] at picked; cases picked; exact b
  · rw [if_neg a, if_neg b] at picked; cases picked

theorem checker_cap_facts (oracle : Oracle) (input : CheckInput) (positive : input.positions.card ≠ 0)
    (state : MachineState) (rows : List PublicRow) (fuel : Nat) (enough : 80000 ≤ fuel)
    (cursor : RecordCursor input input.positions.card state)
    (framed : RecordInputFrame input input.positions.card state)
    (table : CollectedTable oracle input input.positions.card state rows) :
    CheckerCapFacts oracle input state fuel := by
  let groups := Opening.groupsBefore input.positions input.positions.card
  let pointer := checkProofByte input.positions.card
  have ready := checker_cap_ready oracle input state rows cursor table
  have cap := execute_cap_suffix oracle groups state pointer 536871424 fuel ready enough
  have size : groups.length = input.positions.card := record_groups_length input _ (Nat.le_refl _)
  have heapCorrect (message : Message) (salts : CompleteSaltTape) :
      CapHeapCorrect oracle (PackedHonest.honestHeap oracle message salts) := by
    intro node positiveNode below
    unfold PackedHonest.honestHeap
    rw [QuartetCheck.upper_heap_parent _ _ _ node positiveNode (by omega)]
    exact node_keep_238 (by omega) _
  refine ⟨cap.terminates,?_,cap.paths,?_,?_⟩
  · rcases cap.honestCalls with walk | ⟨atEnd, calls⟩
    · rw [size] at walk
      omega
    · rw [size] at calls
      have f := checker_cap_frontier_bound input
      have f' : (capFrontierNodes groups 1 8).length ≤ 128 := f
      have bytes := cap_packed_bytes_le (capFrontierNodes groups 1 8).length
      have e : 13824430176+534*input.positions.card+capPackedBytes (capFrontierNodes groups 1 8).length =
          13824430176+72160 := atEnd
      have kBig : 128 ≤ input.positions.card := by omega
      omega
  · intro message salts canonical
    obtain ⟨data, root, ending⟩ := checker_honest_cap_data oracle input state rows table framed cursor
      positive message salts canonical
    exact cap.honest (PackedHonest.honestHeap oracle message salts) (heapCorrect message salts) data root ending
  · intro message salts near k128 f128
    let heap := PackedHonest.honestHeap oracle message salts
    let nodes := capFrontierNodes groups 1 8
    have fl : nodes.length = 128 := by
      have := f128; unfold honestNodes at this; rwa [List.length_map] at this
    obtain ⟨spine, picked⟩ := full_frontier_pick groups fl
    let u := nodes.getLast?.getD 0
    have uAt : nodes[127]'(by omega) = u := by
      show _ = nodes.getLast?.getD 0
      rw [List.getLast?_eq_getElem?, show nodes.length - 1 = 127 by omega, List.getElem?_eq_getElem (by omega)]
      rfl
    have node : u = 255 ∨ u = 510 ∨ u = 511 := group_pick_node picked
    have hu : 0 < u ∧ u < 256*2 := by rcases node with h | h | h <;> rw [h] <;> decide
    have nodup := frontier_nodup groups 8 1 (by decide)
    let H := heap u
    have high : ∀ i, 238 ≤ i → i < 256 → H.getLsbD i = false := by
      intro i lo hi'
      have proj := PackedHonest.honest_projected238_node oracle message salts u hu.1 (by omega)
      show (PackedHonest.honestHeap oracle message salts u).getLsbD i = false
      rw [← proj]
      simp only [pad238, BitVec.getLsbD_append]
      simp [show ¬ i < 238 by omega]
    let w := pad238 (clearTop H)
    obtain ⟨low, top⟩ := honest_patch H high
    let heap' := fun n => if n = u then w else heap n
    -- the near input's data
    have nearClose : NearHonest input (honestCheckInput oracle message input.positions salts) := by
      rw [near]
      exact near_honest_input oracle message input.positions salts (by omega)
    have rootV : readBuffer state (8*536871424) 32 = heap 1 :=
      (record_input_root input input.positions.card state framed).trans nearClose.commitment
    have endV : state.getReg .x22 = BitVec.ofNat 64 (pointer+capPackedBytes nodes.length) := by
      rw [cursor.proofEnd]
      change BitVec.ofNat 64 (13824430176+input.proof.length) =
        BitVec.ofNat 64 (pointer+capPackedBytes (capFrontierNodes groups 1 8).length)
      rw [nearClose.length, PackedHonest.honest_proof_length,
        checker_honest_cap_nodes input.positions positive, cap_packed_bytes_closed]
      apply congrArg (BitVec.ofNat 64)
      dsimp only [pointer, checkProofByte, groups]
      omega
    have atEndV : pointer+capPackedBytes nodes.length = 13824430176+72160 := by
      dsimp only [pointer, checkProofByte]
      rw [fl, k128]
      decide
    have aboveV : u = 255 → capIsMarked groups 127 2 = true := fun _ => spine
    -- the decoded frontier is the cleared honest one
    have partsNear : input.proof = (honestCheckInput oracle message input.positions salts).proof.take
        (534*input.positions.card) ++ Quartet.packNodes (clearLast (nodes.map heap)) := by
      rw [near]
      rfl
    have widthNear : ((honestCheckInput oracle message input.positions salts).proof.take
        (534*input.positions.card)).length = 534*input.positions.card := by
      rw [List.length_take]
      have := PackedHonest.honest_input_records_fit oracle message input.positions salts
      omega
    have validNear : input.proof.length ≤ PackedChecker.submission.sizes.proof := by
      rw [nearClose.length]
      exact PackedHonest.honest_input_admitted oracle message input.positions salts
    have bytes := packed_frontier_bytes input state framed (clearLast (nodes.map heap)) _ partsNear widthNear validNear
    have contents : CapContents groups state 1 8 pointer 0 heap' := by
      constructor
      · intro leaf seen low' high' _
        have marked : capIsMarked groups leaf 0 = true := by simpa using leaf_mark groups seen 0
        have ne : leaf ≠ u := by
          intro e
          by_cases h255 : u = 255
          · omega
          · rw [e, pick_unmarked picked h255] at marked
            cases marked
        rw [show heap' leaf = heap leaf by simp [heap', ne]]
        exact table.honest message salts nearClose leaf seen
      · intro i bounded
        have member := List.getElem_mem (l := nodes) bounded
        obtain ⟨positiveNode, capNode⟩ := frontier_node_bounds groups 1 8 Opening.cap_span_root _ member
        have decoded := cap_frontier_of_pack state pointer (clearLast (nodes.map heap)) bytes i
          (by rw [clear_last_length, List.length_map]; exact bounded)
        rw [Nat.zero_add, decoded]
        by_cases last : i = 127
        · subst last
          rw [show heap' nodes[127] = w by rw [uAt]; simp [heap']]
          simp only [clearLast, List.length_map, fl, List.getElem!_eq_getElem?_getD]
          simp [List.getElem?_set, uAt, w, H, show 127 < nodes.length by omega]
        · have ne : nodes[i] ≠ u := by
            rw [← uAt]
            intro e
            have := (List.Nodup.getElem_inj_iff nodup).mp e
            omega
          rw [show heap' nodes[i] = heap nodes[i] by simp [heap', ne]]
          simp only [clearLast, List.length_map, fl, List.getElem!_eq_getElem?_getD]
          rw [List.getElem?_set_ne (by omega), List.getElem?_map, List.getElem?_eq_getElem bounded]
          exact PackedHonest.honest_projected238_node oracle message salts _ positiveNode (by
            have e : nodes[i] = (capFrontierNodes groups 1 8)[i] := rfl
            omega)
    by_cases zero : (H.extractLsb' 230 8).toNat = 0
    · -- nothing to restore: the decoded frontier is the honest one
      have same : w = H := clear_zero H high zero
      have plain : heap' = heap := by funext n; by_cases e : n = u <;> simp [heap', e, same, H]
      rw [plain] at contents
      exact cap.honest heap (heapCorrect message salts) contents rootV endV
    · exact cap.nearHonest heap u w (heapCorrect message salts) contents rootV endV atEndV picked aboveV low
        ⟨(H.extractLsb' 230 8).toNat, by omega, by have := BitVec.isLt (H.extractLsb' 230 8); omega, top⟩

end TwoPermutationPrototype.Packed.Checker
