import CommitGolfCandidate.CapOpenRecordsPrefixRead
import CommitGolfCandidate.CapOpenRecordSlots

/-! Every salt/sibling slot emitted by the current record survives the remaining
records. The result still refers to the current entry's heap; the bounded
input frame supplies the later connection to the original ABI trapdoor. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordState

def capLowerSlotAddress (context : CapOpenRecordContext) (position slot : Nat) : Nat :=
  if slot = 0 then context.salts+32*position
  else context.roots+32*(((16777216+position)/2^(slot-1)) ^^^ 1)

theorem cap_open_records_head_slot (context : CapOpenRecordContext)
    (records : List Index) (inputReference : MachineState)
    (countBound : records.length < 2^64)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (outputSpace : context.output+544*records.length ≤ context.limit)
    (inputs : CapOpenRecordInputs context records inputReference)
    (high : 32768 ≤ context.output)
    (heapBelow : context.roots+1073741824 ≤ context.output)
    (saltsBelow : context.salts+536870912 ≤ context.output)
    (remaining : Nat) (state : MachineState)
    (ready : CapOpenRecordsReady context records inputReference (remaining+1) state)
    (slot : Nat) (slotBound : slot < 17) :
    readBuffer (capCountedRun capOpenRecordState (remaining+1) state)
      (context.output+544*(records.length-(remaining+1))+32*slot) 32 =
      readBuffer state (capLowerSlotAddress context
        (records[records.length-(remaining+1)]'(by have bound := ready.bounded; omega)).val
        slot) 32 := by
  have bounded := ready.bounded
  have ordinalBound : records.length-(remaining+1) < records.length := by omega
  let position := (records[records.length-(remaining+1)]'ordinalBound).val
  let cursor := context.output+544*(records.length-(remaining+1))
  have positionBound : position < 16777216 := by
    simpa only [position, LENGTH, LOG_LENGTH, Nat.reducePow] using
      (records[records.length-(remaining+1)]'ordinalBound).isLt
  have loaded := cap_open_records_loaded context records inputReference state remaining
    indexSpace inputs ready
  have aligned : cursor % 8 = 0 := by
    have base := context.outputAligned
    dsimp only [cursor]
    omega
  have space : cursor+544 ≤ context.limit := by
    dsimp only [cursor]
    omega
  have next := cap_open_records_ready_next context records inputReference state remaining
    countBound indexSpace outputSpace inputs ready
  have retained := cap_open_records_prefix_read context records inputReference
    countBound indexSpace outputSpace inputs remaining (capOpenRecordState state) next
    (cursor+32*slot) 32 (by dsimp only [cursor]; omega)
    (by dsimp only [cursor]; omega)
  rw [capCountedRun.eq_2]
  change readBuffer (capCountedRun capOpenRecordState remaining (capOpenRecordState state))
    (cursor+32*slot) 32 = readBuffer state (capLowerSlotAddress context position slot) 32
  rw [retained]
  by_cases salt : slot = 0
  · subst slot
    simp only [Nat.mul_zero, Nat.add_zero, capLowerSlotAddress, ite_true]
    exact cap_open_record_salt_slot context.roots context.salts context.limit cursor position
      state (by simpa using ready.pc) ready.roots ready.salts ready.cursor aligned space
      context.limitBound (by dsimp only [cursor]; omega) context.saltAligned
      (by dsimp only [cursor]; omega) positionBound loaded ready.leaves ready.marks
  · have sibling : slot-1 < 16 := by omega
    have address : cursor+32*slot = cursor+32+32*(slot-1) := by omega
    rw [capLowerSlotAddress, if_neg salt, address]
    exact cap_open_record_sibling_slot context.roots context.limit cursor position
      state (by simpa using ready.pc) ready.roots ready.cursor aligned space
      context.limitBound (by dsimp only [cursor]; omega) context.rootAligned
      (by dsimp only [cursor]; omega) positionBound loaded ready.leaves ready.marks
      (slot-1) sibling

end CommitGolfCandidate
