import CommitGolfCandidate.TwoPermutationPackedRecordLeafMeaning
import CommitGolfCandidate.TwoPermutationPackedRecordLeafBlock
import CommitGolfCandidate.QuartetCheckHonest

namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Packed.Checker
open TwoPermutationPrototype.Checker (honestIndex RecordInputFrame)
open TwoPermutationPrototype.QuartetCertificate (honestCheckInput)
open TwoPermutationPrototype.PackedHonest (honestHeap honestLeaves)
open TwoPermutationPrototype.Checker (checkSourceWord checker_positions_bound)
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000

theorem block_trace (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState) (fits : ProofWithin input)
    (cursor : RecordCursor input ordinal state) (framed : RecordInputFrame input ordinal state) :
    let item := honestIndex input.positions ordinal present
    let observed := block oracle ordinal item.val state
    Nonempty (PackedLeafTrace oracle item.val (input.values item) (readBuffer observed.state 12288 32) observed.rows) := by
  let item := honestIndex input.positions ordinal present
  let raw := (rawLeaf oracle ordinal item.val state).1
  have meaning := raw_digest_rows oracle ordinal item.val state
  have values := raw_message_words input ordinal present state fits cursor framed
  dsimp only at meaning
  rw [values] at meaning
  obtain ⟨rows,digest⟩ := meaning
  have qentry := raw_quartet_entry oracle input ordinal present state fits cursor framed
  let reply := oracle.permutation (qInput raw)
  have slots := q_quartet_slots qentry
  have final := (q_final_memory qentry reply).2
  have enc := q_input_enc qentry
  dsimp only
  refine ⟨⟨rawNonce item.val state,?_,?_,qQuartet raw,reply,?_,?_,?_⟩⟩
  · change _ ∈ (rawLeaf oracle ordinal item.val state).2 ++ (quartetBlock oracle raw).rows
    rw [rows]
    exact List.mem_append_left _ List.mem_cons_self
  · change _ ∈ (rawLeaf oracle ordinal item.val state).2 ++ (quartetBlock oracle raw).rows
    rw [rows]
    exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact slots.1.trans digest
  · change _ ∈ (rawLeaf oracle ordinal item.val state).2 ++ (quartetBlock oracle raw).rows
    apply List.mem_append_right
    change _ ∈ [PublicRow.permutation (qInput raw) (oracle.permutation (qInput raw))]
    rw [← enc]
    exact List.mem_cons_self
  · exact final.symm

theorem block_honest (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState) (fits : ProofWithin input)
    (cursor : RecordCursor input ordinal state) (framed : RecordInputFrame input ordinal state)
    (message : Message) (salts : CompleteSaltTape)
    (canonical : NearHonest input (honestCheckInput oracle message input.positions salts)) :
    let item := honestIndex input.positions ordinal present
    readBuffer (block oracle ordinal item.val state).state 12288 32 =
      honestHeap oracle message salts (Opening.lowerNode (QuartetCheck.flipIndex item.val) 2) := by
  let item := honestIndex input.positions ordinal present
  let raw := (rawLeaf oracle ordinal item.val state).1
  let leaves := honestLeaves oracle message salts
  have qentry := raw_quartet_entry oracle input ordinal present state fits cursor framed
  let reply := oracle.permutation (qInput raw)
  have final := (q_final_memory qentry reply).2
  obtain ⟨leafSlot, siblingSlots⟩ := q_quartet_slots qentry
  have card := checker_positions_bound input
  have room := (packed_record_geometry input ordinal present fits).2.2.2.1
  obtain ⟨_,_,_,wordFrame,_,_⟩ := raw_view oracle input ordinal present state fits cursor framed
  -- the leaf digest at the quartet entry is honest
  have leafDigest : readBuffer raw 12288 32 = Sampling.Quartet.leafAt leaves item.val.val := by
    have digest := (raw_digest_rows oracle ordinal item.val state).2
    rw [digest, raw_message_words input ordinal present state fits cursor framed,
      raw_nonce_honest oracle input ordinal present state fits cursor framed message salts canonical,
      canonical_entry_value oracle input message salts item canonical]
    rw [show Sampling.Quartet.leafAt leaves item.val.val = leaves item.val from dif_pos item.val.isLt]
    exact honest_row_digest oracle message salts item.val
  -- the proof siblings at the quartet entry are the honest neighbouring leaves
  have siblingDigest (j : Nat) (lo : 1 ≤ j) (hi : j ≤ 3) :
      readBuffer raw (checkProofByte ordinal + (16+32*(j-1))) 32 = Sampling.Quartet.leafAt leaves (item.val.val ^^^ j) := by
    have same : readBuffer raw (checkProofByte ordinal + (16+32*(j-1))) 32 =
        readBuffer state (checkProofByte ordinal + (16+32*(j-1))) 32 := by
      apply buffer_byte_frame
      intro i small
      unfold MEMORY_BYTES at room
      exact wordFrame _ (by omega) (Or.inr (by unfold checkSourceWord checkProofByte; omega)) (Or.inr (by
        unfold checkProofByte; omega))
    rw [same, packed_record_quartet_sibling oracle message input.positions salts ordinal (j-1) present (by omega) state canonical framed,
      show j-1+1 = j by omega]
  have bound : item.val.val < 16777216 := item.val.isLt
  have honestQuartet : qQuartet raw = Sampling.Quartet.quartetPayload leaves (item.val.val/4) :=
    QuartetCheck.honest_quartet leaves item.val.val (qQuartet raw) (leafSlot.trans leafDigest)
      (fun j lo hi => (siblingSlots j lo hi).trans (siblingDigest j lo hi))
  dsimp only
  change readBuffer (qFinal raw reply) 12288 32 = _
  rw [final, QuartetCheck.lower_node_two_flip]
  unfold PackedHonest.honestHeap
  rw [QuartetCheck.upper_heap_leaf_flip _ _ _ (item.val.val/4) (by omega)]
  change quartetNode (item.val.val / 4) (oracle.permutation (qInput raw)) = _
  rw [q_input_enc qentry, honestQuartet]
  rfl

end TwoPermutationPrototype.Packed.RecordLeaf
