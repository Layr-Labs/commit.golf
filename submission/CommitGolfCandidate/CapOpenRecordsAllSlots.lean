import CommitGolfCandidate.CapOpenRecordsHeadSlots

/-! All remaining lower-record slots equal the original admitted input slots.
The induction uses absolute list ordinals, so a future record keeps the same
index and output address. Earlier output is protected by the head-slot frame. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordState

private theorem source_window (context : CapOpenRecordContext) (position slot : Nat)
    (positionBound : position < 16777216)
    (rootHigh : 32768 ≤ context.roots) (saltHigh : 32768 ≤ context.salts)
    (heapBelow : context.roots+1073741824 ≤ context.output)
    (saltsBelow : context.salts+536870912 ≤ context.output) :
    32768 ≤ capLowerSlotAddress context position slot ∧
      capLowerSlotAddress context position slot+32 ≤ context.output := by
  unfold capLowerSlotAddress
  split
  · constructor <;> omega
  · have quotient := Nat.div_le_self (16777216+position) (2^(slot-1))
    have siblingBound : ((16777216+position)/2^(slot-1)) ^^^ 1 < 33554432 :=
      Nat.xor_lt_two_pow (n := 25) (by omega) (by decide)
    constructor <;> omega

theorem cap_open_records_all_slots (context : CapOpenRecordContext)
    (records : List Index) (inputReference : MachineState)
    (countBound : records.length < 2^64)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (outputSpace : context.output+544*records.length ≤ context.limit)
    (inputs : CapOpenRecordInputs context records inputReference)
    (rootHigh : 32768 ≤ context.roots) (saltHigh : 32768 ≤ context.salts)
    (heapBelow : context.roots+1073741824 ≤ context.output)
    (saltsBelow : context.salts+536870912 ≤ context.output)
    (remaining : Nat) (state : MachineState)
    (ready : CapOpenRecordsReady context records inputReference remaining state)
    (ordinal : Nat) (inside : ordinal < records.length)
    (notConsumed : records.length-remaining ≤ ordinal)
    (slot : Nat) (slotBound : slot < 17) :
    readBuffer (capCountedRun capOpenRecordState remaining state)
      (context.output+544*ordinal+32*slot) 32 =
      capLowerSlotPayload slot (readBuffer inputReference
        (capLowerSlotAddress context (records[ordinal]'inside).val slot) 32) := by
  induction remaining generalizing state with
  | zero => omega
  | succ remaining ih =>
    have bounded := ready.bounded
    by_cases head : ordinal = records.length-(remaining+1)
    · have entry := cap_open_records_head_slot context records inputReference countBound
        indexSpace outputSpace inputs (by omega) heapBelow saltsBelow remaining state
        ready slot slotBound
      have positionBound : (records[ordinal]'inside).val < 16777216 := by
        simpa only [LENGTH, LOG_LENGTH, Nat.reducePow] using (records[ordinal]'inside).isLt
      have window := source_window context (records[ordinal]'inside).val slot
        positionBound rootHigh saltHigh heapBelow saltsBelow
      have original := cap_open_retained_read context.output inputReference state
        (capLowerSlotAddress context (records[ordinal]'inside).val slot) 32
        window.1 window.2 ready.frame
      subst ordinal
      exact entry.trans (congrArg (capLowerSlotPayload slot) original)
    · have next := cap_open_records_ready_next context records inputReference state remaining
        countBound indexSpace outputSpace inputs ready
      rw [capCountedRun.eq_2]
      exact ih _ next (by omega)

end CommitGolfCandidate
