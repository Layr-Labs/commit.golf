import CommitGolfCandidate.CapOpenRecordMarks
import CommitGolfCandidate.CapOpenPathSlots
import CommitGolfCandidate.S6Tree

/-! Exact digest slots of one record after its occupancy store: the salt field
(slot 0), the three other leaf digests of the group (slots 1..3) and the
fourteen lower siblings (slots 4..17). Each is stated against the record-entry
state; a later bounded retained-input frame connects it to the ABI trapdoor. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
attribute [local irreducible] capOpenRecordGroupState capOpenRecordState
  capOpenRecordPathState capOpenSaltedState

/-- Place in the group cell of record slot 1..3: the places other than `position % 4`, increasing. -/
def capOpenPlace (position slot : Nat) : Nat := if slot - 1 < position % 4 then slot - 1 else slot

/-- Slot 0: the 16 nonce bytes read there, the tag `4072 + 256 * position`, 8 zero bytes. -/
def capLowerSlotPayload (position slot : Nat) (raw : Digest) : Digest :=
  if slot = 0 then BitVec.ofNat 256 (raw.toNat % 2 ^ 128 + (4072 + 256 * position) * 2 ^ 128) else raw

theorem cap_open_place_stub (position k : Nat) :
    capOpenPlace position (k+1) = capStubPlace (position%4) k := by
  simp only [capOpenPlace, capStubPlace, Nat.add_sub_cancel]

theorem cap_lower_slot_payload_salt (state : MachineState) (address : Nat) (index : Index) :
    capLowerSlotPayload index.val 0 (readBuffer state address 32) =
      expandTagged index (readBuffer state address 16) := by
  rw [capLowerSlotPayload, if_pos rfl, expandTagged, s6Tag]
  apply congrArg (fun n => BitVec.ofNat 256 (n + (4072 + 256 * index.val) * 2 ^ 128))
  unfold readBuffer
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have split : ∀ count, (∑ i ∈ Finset.range count,
      (state.getByte (BitVec.ofNat 64 (address + i))).toNat * 2 ^ (8 * i)) < 2^(8*count) := by
    intro count
    induction count with
    | zero => simp
    | succ count ih =>
      rw [Finset.sum_range_succ]
      have byte := (state.getByte (BitVec.ofNat 64 (address + count))).isLt
      have term : (state.getByte (BitVec.ofNat 64 (address + count))).toNat * 2 ^ (8 * count) ≤
          255 * 2^(8*count) := Nat.mul_le_mul_right _ (by omega)
      rw [show 8*(count+1) = 8*count + 8 by ring, Nat.pow_add]
      omega
  have low := split 16
  have whole := split 32
  rw [Nat.mod_eq_of_lt whole, Nat.mod_eq_of_lt low]
  rw [show 32 = 16 + 16 from rfl, Finset.sum_range_add]
  have high : (∑ i ∈ Finset.range 16,
      (state.getByte (BitVec.ofNat 64 (address + (16 + i)))).toNat * 2 ^ (8 * (16 + i))) =
      2^128 * (∑ i ∈ Finset.range 16,
        (state.getByte (BitVec.ofNat 64 (address + (16 + i)))).toNat * 2 ^ (8 * i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show 8*(16+i) = 128 + 8*i by ring, Nat.pow_add]
    ring
  rw [high, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt low]

theorem cap_open_record_store_read {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state)
    (address : Nat) (bounded : address < 2^64) (high : 32768 ≤ address) :
    (capOpenRecordState state).getMem (BitVec.ofNat 64 address) =
      (capOpenRecordGroupState state).getMem (BitVec.ofNat 64 address) := by
  have marks : (capOpenRecordGroupState state).getReg .x22 = 28672 :=
    (cap_open_record_group_register state .x22 (by decide) entry).trans entry.marks
  have memory := cap_open_group_memory (capOpenRecordGroupState state) (256+position/65536) marks
    (cap_open_record_group_index entry)
  have different : BitVec.ofNat 64 address ≠ BitVec.ofNat 64 (28672+8*(256+position/65536)) :=
    cap_stub_word_ne _ _ bounded (by have := entry.positionBound; omega)
      (by have := entry.positionBound; omega)
  have viaStore : (capOpenRecordState state).getMem (BitVec.ofNat 64 address) =
      ((capOpenRecordGroupState state).setMem (BitVec.ofNat 64 (28672+8*(256+position/65536)))
        ((capOpenRecordGroupState state).getReg .x31)).getMem (BitVec.ofNat 64 address) := by
    rw [capOpenRecordState]
    exact cap_open_get_mem_of_mem memory _
  rw [viaStore, cap_open_set_mem_get, if_neg different]

/-- Words of the trapdoor (below the cursor) are the same at the path entry as at the record entry. -/
theorem cap_open_record_path_low_word {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state)
    (address : Nat) (below : address < cursor) :
    (capOpenRecordPathState state).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  have small := cap_open_record_at_small entry
  rw [(cap_open_record_path_facts entry).2.2.2.2.2.2 address (by omega) (by omega), capOpenSaltedState,
    cap_nonce_eight_memory_outside]
  · rfl
  · intro word equal
    rw [cap_open_record_prepare_register state 3 (by decide) .x25 (by decide), entry.pointer,
      ← BitVec.ofNat_add] at equal
    exact cap_stub_word_ne _ _ (by omega) (by have := word.isLt; omega) (by have := word.isLt; omega) equal

theorem cap_open_record_salt_slot {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state)
    (zero : state.getMem (BitVec.ofNat 64 (cursor+24)) = 0) :
    readBuffer (capOpenRecordState state) cursor 32 =
      capLowerSlotPayload position 0 (readBuffer state (saltBase+16*position) 32) := by
  have small := cap_open_record_at_small entry
  have aligned := entry.cursorAligned
  have high := entry.high
  have saltBelow := entry.saltBelow
  have facts := cap_open_record_path_facts entry
  have toSalted (offset : Nat) (inside : offset < 24) (offsetAligned : offset % 8 = 0) :
      (capOpenRecordState state).getMem (BitVec.ofNat 64 (cursor+offset)) =
        (capNonceEightState (capOpenRecordPrefix state 3)).getMem (BitVec.ofNat 64 (cursor+offset)) := by
    have low := cap_open_record_group_low_read entry (cursor+offset) 32 (by omega)
    have word := congrArg (fun digest : Digest => digest.extractLsb' 0 64) low
    simp only [read_digest_word _ _ 0 (by omega : (cursor+offset) % 8 = 0) (by decide), Nat.mul_zero,
      Nat.add_zero] at word
    rw [cap_open_record_store_read entry _ (by omega) (by omega), word,
      facts.2.2.2.2.2.2 _ (by omega) (by omega), capOpenSaltedState]
  have source := cap_open_record_salt_address state position saltBase entry.loaded entry.salts
    entry.stride
  have destination := (cap_open_record_prepare_register state 3 (by decide) .x25
    (by decide)).trans entry.pointer
  have index : (capOpenRecordPrefix state 3).getReg .x20 = BitVec.ofNat 64 position := by
    rw [cap_open_record_index, entry.loaded]
  have nonce := cap_nonce_eight_words (capOpenRecordPrefix state 3) (saltBase+16*position) cursor
    position source destination index (by have := entry.positionBound; omega) (by omega) (by omega)
    (Or.inl (by omega))
  have prepared (address : Word) : (capOpenRecordPrefix state 3).getMem address = state.getMem address := by
    simp only [MachineState.getMem, cap_open_record_prepare_memory state 3 (by decide)]
  have w0 := toSalted 0 (by decide) (by decide)
  have w1 := toSalted 8 (by decide) (by decide)
  have w2 := toSalted 16 (by decide) (by decide)
  rw [Nat.add_zero, nonce.1, prepared] at w0
  rw [nonce.2.1, prepared] at w1
  rw [nonce.2.2.1] at w2
  have w3 := cap_open_record_high_word entry (cursor+24) (by omega) (by omega) (Or.inl rfl)
  rw [zero] at w3
  have saltAligned : (saltBase+16*position) % 8 = 0 := by have := entry.saltAligned; omega
  rw [read_digest_words _ _ aligned, w0, w1, w2, w3, capLowerSlotPayload, if_pos rfl,
    read_digest_words _ _ saltAligned]
  exact cap_nonce_salt_field _ _ _ _ (4072+256*position) (by have := entry.positionBound; omega)

theorem cap_open_record_other_slot {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state)
    (k : Nat) (hk : k < 3) :
    readBuffer (capOpenRecordState state) (cursor+32+32*k) 32 =
      readBuffer state (rootBase+268435784+368*(position/4)+32*capStubPlace (position%4) k) 32 := by
  have small := cap_open_record_at_small entry
  have aligned := entry.cursorAligned
  have high := entry.high
  have facts := cap_open_record_path_facts entry
  have toPath : readBuffer (capOpenRecordState state) (cursor+32+32*k) 32 =
      readBuffer (capOpenRecordPathState state) (cursor+32+32*k) 32 := by
    rw [← cap_open_record_group_low_read entry (cursor+32+32*k) 32 (by omega)]
    apply read_digest_congr _ _ _ (by omega)
    intro i hi
    exact cap_open_record_store_read entry _ (by omega) (by omega)
  have word (w : Nat) (hw : w < 4) :
      (capOpenRecordPathState state).getMem (BitVec.ofNat 64 (cursor+32+32*k+8*w)) =
        state.getMem (BitVec.ofNat 64 (rootBase+268435784+368*(position/4)+32*capStubPlace (position%4) k+8*w)) :=
    facts.2.2.2.2.2.1 k hk w hw
  have e0 := word 0 (by decide)
  have e1 := word 1 (by decide)
  have e2 := word 2 (by decide)
  have e3 := word 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul] at e0 e1 e2 e3
  have sourceAligned : (rootBase+268435784+368*(position/4)+32*capStubPlace (position%4) k) % 8 = 0 := by
    have := entry.rootAligned
    omega
  rw [toPath, read_digest_words _ _ (by omega), read_digest_words _ _ sourceAligned, e0, e1, e2, e3]

theorem cap_open_record_sibling_slot {rootBase saltBase cursor limit position : Nat}
    {state : MachineState} (entry : CapOpenRecordAt rootBase saltBase cursor limit position state)
    (ordinal : Nat) (ordinalBound : ordinal < 14) :
    readBuffer (capOpenRecordState state) (cursor+128+32*ordinal) 32 =
      readBuffer state (rootBase+32*(((4194304+position/4)/2^ordinal) ^^^ 1)) 32 := by
  have small := cap_open_record_at_small entry
  have aligned := entry.cursorAligned
  have high := entry.high
  have heapBelow := entry.heapBelow
  have facts := cap_open_record_path_facts entry
  have ready := cap_open_record_path_ready entry
  have pathCursor : ((capOpenRecordPathState state).getReg .x25).toNat = cursor+128 := by
    rw [facts.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cursor+128 < 2^64)]
  have slots := cap_open_path_loop_slots rootBase limit (cursor+128) 14
    (4194304+position/4) (capOpenRecordPathState state) (capOpenRecordPathState state)
    entry.limitBound entry.rootAligned (by omega) ready (by have := entry.positionBound; omega) facts.2.1
    (by have := pathCursor; omega) (fun _ _ => rfl) ordinal ordinalBound
  rw [pathCursor, ← capOpenRecordGroupState] at slots
  have quotient := Nat.div_le_self (4194304+position/4) (2^ordinal)
  have siblingBound : ((4194304+position/4)/2^ordinal) ^^^ 1 < 33554432 :=
    Nat.xor_lt_two_pow (n := 25) (by have := entry.positionBound; omega) (by decide)
  have rootAligned := entry.rootAligned
  have toGroup : readBuffer (capOpenRecordState state) (cursor+128+32*ordinal) 32 =
      readBuffer (capOpenRecordGroupState state) (cursor+128+32*ordinal) 32 := by
    apply read_digest_congr _ _ _ (by omega)
    intro i hi
    exact cap_open_record_store_read entry _ (by omega) (by omega)
  have toState : readBuffer (capOpenRecordPathState state)
      (rootBase+32*(((4194304+position/4)/2^ordinal) ^^^ 1)) 32 =
      readBuffer state (rootBase+32*(((4194304+position/4)/2^ordinal) ^^^ 1)) 32 := by
    apply read_digest_congr _ _ _ (by omega)
    intro i hi
    exact cap_open_record_path_low_word entry _ (by omega)
  rw [toGroup, slots, toState]

end CommitGolfCandidate
