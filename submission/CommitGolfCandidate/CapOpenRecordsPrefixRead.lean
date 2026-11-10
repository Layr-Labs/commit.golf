import CommitGolfCandidate.CapOpenRecordsPrefixFrame

/-! Read an already emitted block after the remaining records. The block must
end before the current cursor. This is the byte-level preservation connector
for individual lower-record slot theorems; no new output value is assumed. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_open_records_prefix_read (context : CapOpenRecordContext)
    (records : List Index) (inputReference : MachineState)
    (countBound : records.length < 2^64)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (outputSpace : context.output+576*records.length ≤ context.limit)
    (inputs : CapOpenRecordInputs context records inputReference)
    (remaining : Nat) (state : MachineState)
    (ready : CapOpenRecordsReady context records inputReference remaining state)
    (address count : Nat) (high : 22528 ≤ address)
    (inside : address+count ≤ context.output+576*(records.length-remaining)) :
    readBuffer (capCountedRun capOpenRecordState remaining state) address count =
      readBuffer state address count := by
  exact cap_open_retained_read _ state _ address count high inside
    (cap_open_records_prefix_frame context records inputReference state countBound
      indexSpace outputSpace inputs remaining state ready
      (context.output+576*(records.length-remaining)) (Nat.le_refl _)
      (cap_open_retained_refl _ _))

end CommitGolfCandidate
