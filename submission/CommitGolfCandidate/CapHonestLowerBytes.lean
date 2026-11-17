import CommitGolfCandidate.CapHonestLower
import CommitGolfCandidate.CapOpenLowerBytes
import Mathlib.Data.List.OfFn

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] readBuffer

def capHonestLowerRecords (message : Message) (committed : MachineState)
    (positions : Positions) : List CapLowerRecord :=
  (capOpenRequestedIndices positions).map (capHonestLowerRecord message committed)

theorem cap_honest_lower_encoding_length (record : CapLowerRecord) :
    (capLowerEncoding record).length = 17 := by
  simp only [capLowerEncoding, List.length_cons, List.length_ofFn]

private theorem encoding_sibling (record : CapLowerRecord) (level : Nat)
    (inside : level < 16) :
    (capLowerEncoding record)[level+1]'(by
      rw [cap_honest_lower_encoding_length]; omega) = record.sibling ⟨level, inside⟩ := by
  simp only [capLowerEncoding, List.getElem_cons_succ, List.getElem_ofFn]

theorem cap_honest_lower_loaded_slot (message : Message) (committed : MachineState)
    (positions : Positions) (index : Index) (slot : Nat) (inside : slot < 17) :
    capLowerSlotPayload slot (readBuffer (capProgram.initialState .opening
      (readBuffer committed capProgram.layout.trapdoor capProgram.sizes.trapdoor, positions))
      (capLowerSlotAddress capOpenAbiRecordContext index.val slot) 32) =
      (capLowerEncoding (capHonestLowerRecord message committed index))[slot]'(by
        rw [cap_honest_lower_encoding_length]; exact inside) := by
  have bounded : index.val < 16777216 := index.isLt
  have rootBase : capProgram.layout.trapdoor = 4294971424 := rfl
  have contextRoot : capOpenAbiRecordContext.roots = capProgram.layout.trapdoor := rfl
  have contextSalt : capOpenAbiRecordContext.salts = 5368713248 := rfl
  cases slot with
  | zero =>
    have read := cap_open_input_trapdoor_roundtrip committed positions
      (1073741824+24*index.val) (by change _ ≤ 1610612736; omega)
    rw [capLowerSlotPayload, if_pos rfl, capLowerSlotAddress, if_pos rfl, contextSalt]
    simp only [capLowerEncoding, List.getElem_cons_zero, capHonestLowerRecord, readNonce]
    have address : capProgram.layout.trapdoor+(1073741824+24*index.val) =
        5368713248+24*index.val := by rw [rootBase]; omega
    rw [address] at read
    exact congrArg (fun value : Digest => expandNonce192 (value.extractLsb' 0 192)) read
  | succ slot =>
    have quotient := Nat.div_le_self (16777216+index.val) (2^slot)
    have sibling : ((16777216+index.val)/2^slot) ^^^ 1 < 33554432 :=
      Nat.xor_lt_two_pow (n := 25) (by omega) (by decide)
    have read := cap_open_input_trapdoor_roundtrip committed positions
      (32*(((16777216+index.val)/2^slot) ^^^ 1))
      (by change _ ≤ 1610612736; omega)
    rw [capLowerSlotPayload, if_neg (Nat.succ_ne_zero slot),
      capLowerSlotAddress, if_neg (Nat.succ_ne_zero slot), contextRoot,
      Nat.add_sub_cancel, encoding_sibling _ slot (by omega)]
    change readBuffer _ (capProgram.layout.trapdoor+
      32*(((16777216+index.val)/2^slot) ^^^ 1)) 32 =
      heapDigest committed 4294971424 (((LENGTH+index.val)/2^slot) ^^^ 1)
    simpa only [heapDigest, rootBase, LENGTH, LOG_LENGTH, Nat.reducePow] using read

theorem cap_honest_lower_loaded_record (message : Message) (committed : MachineState)
    (positions : Positions) (index : Index) :
    (List.ofFn fun slot : Fin 17 =>
      capLowerSlotPayload slot.val (readBuffer (capProgram.initialState .opening
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
  have divided : (17*ordinal.val+slot.val)/17 = ordinal.val := by omega
  have remainder : (17*ordinal.val+slot.val)%17 = slot.val := by omega
  simp only [divided, remainder]

end CommitGolfCandidate
