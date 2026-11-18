import CommitGolfCandidate.CapOpenRecordsPrefixRead
import CommitGolfCandidate.CapOpenRecordSlots

/-! Every slot emitted by the current record survives the remaining records:
the salt field, the three other leaf digests of the group and the fourteen
lower siblings. The result still refers to the current entry's memory; the
bounded input frame supplies the later connection to the original ABI trapdoor. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordState

/-- Source of record slot `slot` of `position`: its nonce (slot 0), the group cell's other
leaf digests (slots 1..3) and the heap siblings of its group node (slots 4..17). -/
def capLowerSlotAddress (context : CapOpenRecordContext) (position slot : Nat) : Nat :=
  if slot = 0 then context.salts + 16 * position
  else if slot < 4 then context.roots + 268435784 + 368 * (position / 4) + 32 * capOpenPlace position slot
  else context.roots + 32 * (((4194304 + position / 4) / 2 ^ (slot - 4)) ^^^ 1)

theorem cap_open_records_head_slot (context : CapOpenRecordContext)
    (records : List Index) (inputReference : MachineState)
    (countBound : records.length < 2^64)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (outputSpace : context.output+576*records.length ≤ context.limit)
    (heapBelow : context.roots+2147483648 ≤ context.output)
    (saltsBelow : context.salts+536870912 ≤ context.output)
    (inputs : CapOpenRecordInputs context records inputReference)
    (remaining : Nat) (state : MachineState)
    (ready : CapOpenRecordsReady context records inputReference (remaining+1) state)
    (slot : Nat) (slotBound : slot < 18) :
    readBuffer (capCountedRun capOpenRecordState (remaining+1) state)
      (context.output+576*(records.length-(remaining+1))+32*slot) 32 =
      capLowerSlotPayload (records[records.length-(remaining+1)]'(by
          have bound := ready.bounded
          omega)).val slot
        (readBuffer state (capLowerSlotAddress context
          (records[records.length-(remaining+1)]'(by have bound := ready.bounded; omega)).val
          slot) 32) := by
  have bounded := ready.bounded
  have ordinalBound : records.length-(remaining+1) < records.length := by omega
  have entry := cap_open_records_entry context records inputReference state remaining
    indexSpace outputSpace heapBelow saltsBelow inputs ready
  generalize (records[records.length-(remaining+1)]'ordinalBound).val = position at entry ⊢
  generalize hcursor : context.output+576*(records.length-(remaining+1)) = cursor at entry ⊢
  have consumed : cursor+576 ≤ context.output+576*(records.length-remaining) := by
    rw [← hcursor]
    have step : 576*(records.length-(remaining+1))+576 = 576*(records.length-remaining) := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    omega
  have high := entry.high
  have space := entry.space
  have next := cap_open_records_ready_next context records inputReference state remaining
    countBound indexSpace outputSpace heapBelow saltsBelow inputs ready
  have retained := cap_open_records_prefix_read context records inputReference
    countBound indexSpace outputSpace heapBelow saltsBelow inputs remaining
    (capOpenRecordState state) next (cursor+32*slot) 32 (by omega) (by omega)
  rw [capCountedRun.eq_2]
  change readBuffer (capCountedRun capOpenRecordState remaining (capOpenRecordState state))
    (cursor+32*slot) 32 = _
  rw [retained]
  by_cases salt : slot = 0
  · subst slot
    have aligned := entry.cursorAligned
    have zero := ready.fresh (cursor+24) (by omega) (by omega) (by omega)
    rw [Nat.mul_zero, Nat.add_zero, capLowerSlotAddress, if_pos rfl]
    exact cap_open_record_salt_slot entry zero
  · have payload : ∀ raw, capLowerSlotPayload position slot raw = raw := by
      intro raw
      rw [capLowerSlotPayload, if_neg salt]
    rw [payload]
    by_cases group : slot < 4
    · obtain ⟨k, rfl⟩ : ∃ k, slot = k+1 := ⟨slot-1, by omega⟩
      have hk : k < 3 := by omega
      have address : capLowerSlotAddress context position (k+1) =
          context.roots+268435784+368*(position/4)+32*capStubPlace (position%4) k := by
        rw [capLowerSlotAddress, if_neg salt, if_pos group, cap_open_place_stub]
      rw [address, show cursor+32*(k+1) = cursor+32+32*k by ring]
      exact cap_open_record_other_slot entry k hk
    · obtain ⟨ordinal, rfl⟩ : ∃ ordinal, slot = ordinal+4 := ⟨slot-4, by omega⟩
      have ordinalBound : ordinal < 14 := by omega
      have address : capLowerSlotAddress context position (ordinal+4) =
          context.roots+32*(((4194304+position/4)/2^ordinal) ^^^ 1) := by
        rw [capLowerSlotAddress, if_neg salt, if_neg group, Nat.add_sub_cancel]
      rw [address, show cursor+32*(ordinal+4) = cursor+128+32*ordinal by ring]
      exact cap_open_record_sibling_slot entry ordinal ordinalBound

end CommitGolfCandidate
