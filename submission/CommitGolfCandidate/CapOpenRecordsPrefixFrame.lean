import CommitGolfCandidate.CapOpenRecordsLoop

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordState

theorem cap_open_records_prefix_frame (context : CapOpenRecordContext)
    (records : List Index) (inputReference outputReference : MachineState)
    (countBound : records.length < 2^64)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (outputSpace : context.output+544*records.length ≤ context.limit)
    (inputs : CapOpenRecordInputs context records inputReference)
    (remaining : Nat) (state : MachineState)
    (ready : CapOpenRecordsReady context records inputReference remaining state)
    (floor : Nat)
    (before : floor ≤ context.output+544*(records.length-remaining))
    (frame : CapOpenRetainedInputs floor outputReference state) :
    CapOpenRetainedInputs floor outputReference
      (capCountedRun capOpenRecordState remaining state) := by
  induction remaining generalizing state with
  | zero => exact frame
  | succ remaining ih =>
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
    have step := cap_open_record_retained_inputs floor context.roots context.limit
      cursor position state outputReference (by simpa using ready.pc)
      ready.roots ready.cursor aligned space context.limitBound before
      positionBound loaded ready.leaves ready.marks frame
    have next := cap_open_records_ready_next context records inputReference state remaining
      countBound indexSpace outputSpace inputs ready
    rw [capCountedRun.eq_2]
    exact ih _ next (by omega) step

end CommitGolfCandidate
