import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.TwoPermutationPackedCheckerBody
import CommitGolfCandidate.TwoPermutationPackedCapComplete
import CommitGolfCandidate.K3C4CapHonest

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
    exact table.honest message salts canonical leaf seen
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

theorem checker_cap_facts (oracle : Oracle) (input : CheckInput) (positive : input.positions.card ≠ 0)
    (state : MachineState) (rows : List PublicRow) (fuel : Nat) (enough : 40000 ≤ fuel)
    (cursor : RecordCursor input input.positions.card state)
    (framed : RecordInputFrame input input.positions.card state)
    (table : CollectedTable oracle input input.positions.card state rows) :
    CheckerCapFacts oracle input state fuel := by
  let groups := Opening.groupsBefore input.positions input.positions.card
  let pointer := checkProofByte input.positions.card
  have ready := checker_cap_ready oracle input state rows cursor table
  have cap := execute_cap_suffix oracle groups state pointer 536871424 fuel ready enough
  refine ⟨cap.terminates,?_,cap.paths,?_⟩
  · have calls := cap.honestCalls
    rw [show groups.length = input.positions.card from record_groups_length input _ (Nat.le_refl _)] at calls
    exact calls
  · intro message salts canonical
    obtain ⟨data, root, ending⟩ := checker_honest_cap_data oracle input state rows table framed cursor
      positive message salts canonical
    have heapCorrect : CapHeapCorrect oracle (PackedHonest.honestHeap oracle message salts) := by
      intro node positiveNode below
      unfold PackedHonest.honestHeap
      rw [QuartetCheck.upper_heap_parent _ _ _ node positiveNode (by omega)]
      exact node_keep_238 (by omega) _
    exact cap.honest (PackedHonest.honestHeap oracle message salts) heapCorrect data root ending

end TwoPermutationPrototype.Packed.Checker
