import CommitGolfCandidate.CapHonestLower
import CommitGolfCandidate.CapOpenLowerBytes
import Mathlib.Data.List.OfFn

/-! Each loaded eighteen-digest record is precisely the honest tagged salt, the
three other cell digests and fourteen stored siblings. Flattening these records
identifies the actual opening prefix with the logical lower-record transcript,
including its order. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
attribute [local irreducible] readBuffer

def capHonestLowerRecords (message : Message) (committed : MachineState)
    (positions : Positions) : List CapLowerRecord :=
  (capOpenRequestedIndices positions).map (capHonestLowerRecord message committed)

theorem cap_honest_lower_encoding_length (record : CapLowerRecord) :
    (capLowerEncoding record).length = 18 := by
  simp only [capLowerEncoding, List.length_cons, List.length_append, List.length_ofFn]

private theorem encoding_other (record : CapLowerRecord) (place : Nat) (inside : place < 3) :
    (capLowerEncoding record)[place+1]'(by
      rw [cap_honest_lower_encoding_length]; omega) = record.others ⟨place, inside⟩ := by
  simp only [capLowerEncoding, List.getElem_cons_succ]
  rw [List.getElem_append_left (by simp only [List.length_ofFn]; exact inside),
    List.getElem_ofFn]

private theorem encoding_sibling (record : CapLowerRecord) (level : Nat) (inside : level < 14) :
    (capLowerEncoding record)[level+4]'(by
      rw [cap_honest_lower_encoding_length]; omega) = record.sibling ⟨level, inside⟩ := by
  simp only [capLowerEncoding, show level+4 = (level+3)+1 by omega, List.getElem_cons_succ]
  rw [List.getElem_append_right (by simp only [List.length_ofFn]; omega)]
  simp only [List.length_ofFn, List.getElem_ofFn, Nat.add_sub_cancel]

theorem cap_honest_lower_loaded_slot (message : Message) (committed : MachineState)
    (positions : Positions) (index : Index) (slot : Nat) (inside : slot < 18) :
    capLowerSlotPayload index.val slot (readBuffer (capProgram.initialState .opening
      (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor, positions))
      (capLowerSlotAddress capOpenAbiRecordContext index.val slot) 32) =
      (capLowerEncoding (capHonestLowerRecord message committed index))[slot]'(by
        rw [cap_honest_lower_encoding_length]; exact inside) := by
  have bounded : index.val < 16777216 := index.isLt
  have rootBase : capProgram.layout.trapdoor = 4294971424 := rfl
  have size : capProgram.sizes.trapdoor = 2147483648 := rfl
  have contextRoot : capOpenAbiRecordContext.roots = capProgram.layout.trapdoor := rfl
  have contextSalt : capOpenAbiRecordContext.salts = capProgram.layout.trapdoor+1811939584 := rfl
  by_cases zero : slot = 0
  · subst slot
    have read := cap_open_input_trapdoor_roundtrip committed positions
      (1811939584+16*index.val) (by rw [size]; omega)
    rw [capLowerSlotAddress, if_pos rfl, contextSalt, Nat.add_assoc, read,
      cap_lower_slot_payload_salt]
    simp only [capLowerEncoding, List.getElem_cons_zero, capHonestLowerRecord, committedNonce]
    rw [rootBase, show 4294971424+(1811939584+16*index.val) = 6106911008+16*index.val by omega]
  · by_cases cell : slot < 4
    · have place : capOpenPlace index.val slot < 4 := by
        unfold capOpenPlace
        split <;> omega
      have read := cap_open_input_trapdoor_roundtrip committed positions
        (268435784+368*(index.val/4)+32*capOpenPlace index.val slot) (by rw [size]; omega)
      rw [capLowerSlotAddress, if_neg zero, if_pos cell, contextRoot,
        show capProgram.layout.trapdoor+268435784+368*(index.val/4)+
          32*capOpenPlace index.val slot = capProgram.layout.trapdoor+(268435784+
          368*(index.val/4)+32*capOpenPlace index.val slot) by omega, read]
      unfold capLowerSlotPayload
      rw [if_neg zero]
      obtain ⟨other, rfl⟩ : ∃ other, slot = other+1 := ⟨slot-1, by omega⟩
      rw [encoding_other _ other (by omega)]
      simp only [capHonestLowerRecord, capHonestCellAddress]
      rw [rootBase]
      congr 1
      omega
    · have level : slot-4 < 14 := by omega
      have quotient := Nat.div_le_self (4194304+index.val/4) (2^(slot-4))
      have sibling : ((4194304+index.val/4)/2^(slot-4)) ^^^ 1 < 8388608 :=
        Nat.xor_lt_two_pow (n := 23) (by omega) (by decide)
      have read := cap_open_input_trapdoor_roundtrip committed positions
        (32*(((4194304+index.val/4)/2^(slot-4)) ^^^ 1)) (by rw [size]; omega)
      rw [capLowerSlotAddress, if_neg zero, if_neg cell, contextRoot, read]
      unfold capLowerSlotPayload
      rw [if_neg zero]
      obtain ⟨deep, rfl⟩ : ∃ deep, slot = deep+4 := ⟨slot-4, by omega⟩
      rw [encoding_sibling _ deep (by omega)]
      simp only [capHonestLowerRecord, heapDigest, Nat.add_sub_cancel]
      rw [rootBase]

theorem cap_honest_lower_loaded_record (message : Message) (committed : MachineState)
    (positions : Positions) (index : Index) :
    (List.ofFn fun slot : Fin 18 =>
      capLowerSlotPayload index.val slot.val (readBuffer (capProgram.initialState .opening
        (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor, positions))
        (capLowerSlotAddress capOpenAbiRecordContext index.val slot.val) 32)) =
      capLowerEncoding (capHonestLowerRecord message committed index) := by
  apply List.ext_getElem
  · rw [List.length_ofFn, cap_honest_lower_encoding_length]
  · intro slot leftBound rightBound
    simp only [List.getElem_ofFn]
    exact cap_honest_lower_loaded_slot message committed positions index slot leftBound

theorem cap_honest_lower_loaded_transcript (message : Message) (committed : MachineState)
    (positions : Positions) :
    capOpenLowerDigests
      (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor) positions =
      capLowerTranscript (capHonestLowerRecords message committed positions) := by
  rw [capOpenLowerDigests, List.ofFn_mul']
  simp only [capLowerTranscript, capHonestLowerRecords, List.flatMap_map]
  rw [List.flatMap_def]
  have enumerated : (capOpenRequestedIndices positions) =
      List.ofFn (fun ordinal : Fin positions.card =>
        (capOpenRequestedIndices positions)[ordinal.val]'(by
          simpa only [capOpenRequestedIndices, Finset.length_sort] using ordinal.isLt)) := by
    apply List.ext_getElem
    · simp only [capOpenRequestedIndices, Finset.length_sort, List.length_ofFn]
    · intro ordinal leftBound rightBound
      simp only [List.getElem_ofFn]
  conv_rhs => rw [enumerated, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext ordinal
  have same : (capOpenRequestedIndices positions).length = positions.card := by
    simp only [capOpenRequestedIndices, Finset.length_sort]
  change _ = capLowerEncoding (capHonestLowerRecord message committed
    ((capOpenRequestedIndices positions)[ordinal.val]'(by omega)))
  rw [← cap_honest_lower_loaded_record message committed positions]
  apply congrArg List.ofFn
  funext slot
  have divided : (18*ordinal.val+slot.val)/18 = ordinal.val := by omega
  have remainder : (18*ordinal.val+slot.val)%18 = slot.val := by omega
  simp only [divided, remainder]

end CommitGolfCandidate
