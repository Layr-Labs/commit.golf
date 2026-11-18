import CommitGolfCandidate.CapOpenRecordsLoop

/-! Later records preserve the high bytes of an already emitted prefix. The
chosen floor may exceed the original proof base, but must lie below the current
cursor. The low occupancy stores are excluded by the high interval. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordState

theorem cap_open_records_prefix_frame (context : CapOpenRecordContext)
    (records : List Index) (inputReference outputReference : MachineState)
    (countBound : records.length < 2^64)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (outputSpace : context.output+576*records.length ≤ context.limit)
    (heapBelow : context.roots+2147483648 ≤ context.output)
    (saltsBelow : context.salts+536870912 ≤ context.output)
    (inputs : CapOpenRecordInputs context records inputReference)
    (remaining : Nat) (state : MachineState)
    (ready : CapOpenRecordsReady context records inputReference remaining state)
    (floor : Nat)
    (before : floor ≤ context.output+576*(records.length-remaining))
    (frame : CapOpenRetainedInputs floor outputReference state) :
    CapOpenRetainedInputs floor outputReference
      (capCountedRun capOpenRecordState remaining state) := by
  induction remaining generalizing state with
  | zero => exact frame
  | succ remaining ih =>
    have bounded := ready.bounded
    have entry := cap_open_records_entry context records inputReference state remaining
      indexSpace outputSpace heapBelow saltsBelow inputs ready
    have step := cap_open_record_retained_inputs floor entry outputReference before frame
    have next := cap_open_records_ready_next context records inputReference state remaining
      countBound indexSpace outputSpace heapBelow saltsBelow inputs ready
    rw [capCountedRun.eq_2]
    exact ih _ next (by omega) step

end CommitGolfCandidate
