import CommitGolfCandidate.CapOpenRecordsAllSlots
import CommitGolfCandidate.CapOpenFilledMarks

/-! Exact lower-record digest slots in the actual ABI opening. Each source is
read from the original loaded trapdoor, not from a hypothetical unchanged mark
array or a later message state. Codec/root correctness remains separate. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_open_loaded_record_slot
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (positive : 0 < positions.card) (ordinal : Nat) (inside : ordinal < positions.card)
    (slot : Nat) (slotBound : slot < 18) :
    readBuffer (capOpenRecordsFinal trapdoor positions)
      (capProgram.layout.proof+576*ordinal+32*slot) 32 =
      capLowerSlotPayload ((capOpenRequestedIndices positions)[ordinal]'(by
          simpa only [capOpenRequestedIndices, Finset.length_sort] using inside)).val slot
        (readBuffer (capProgram.initialState .opening (trapdoor, positions))
        (capLowerSlotAddress capOpenAbiRecordContext
          ((capOpenRequestedIndices positions)[ordinal]'(by
            simpa only [capOpenRequestedIndices, Finset.length_sort] using inside)).val slot)
        32) := by
  have windows := cap_open_abi_record_windows positions
  have below := cap_open_abi_record_below
  have actual := cap_open_records_all_slots capOpenAbiRecordContext
    (capOpenRequestedIndices positions)
    (capProgram.initialState .opening (trapdoor, positions))
    windows.1 windows.2.1 windows.2.2 below.1 below.2
    (cap_open_abi_record_inputs trapdoor positions)
    (by decide) (by decide) positions.card _
    (cap_open_abi_record_ready trapdoor positions positive) ordinal
    (by simpa only [capOpenRequestedIndices, Finset.length_sort] using inside)
    (by simp only [capOpenRequestedIndices, Finset.length_sort, Nat.sub_self]; omega)
    slot slotBound
  simpa only [capOpenRecordsFinal, capOpenAbiRecordContext] using actual

end CommitGolfCandidate
