import CommitGolfCandidate.CapOpenRecordsNext
import CommitGolfCandidate.CostedCountedLoop

/-! Actual counted record pass, with no compression queries. Every callback
derives the record entry from the retained reference interval and checks the
salt/output ranges. The zero residual is the already-reached mark-header PC,
not the opening ABI's separate empty-request branch. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordState

theorem cap_open_records_loop_execute (context : CapOpenRecordContext)
    (records : List Index) (reference : MachineState)
    (countBound : records.length < 2^64)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (outputSpace : context.output+576*records.length ≤ context.limit)
    (heapBelow : context.roots+2147483648 ≤ context.output)
    (saltsBelow : context.salts+536870912 ≤ context.output)
    (inputs : CapOpenRecordInputs context records reference)
    (remaining : Nat) (state : MachineState)
    (ready : CapOpenRecordsReady context records reference remaining state)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (278*remaining+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capCountedRun capOpenRecordState remaining state) allowCoins
          return result.charge (284*remaining) 0) := by
  apply cap_counted_run_execute_costed _ 278 284 capOpenRecordState
    (CapOpenRecordsReady context records reference)
    (fun residual current currentReady =>
      cap_open_records_ready_next context records reference current residual
        countBound indexSpace outputSpace heapBelow saltsBelow inputs currentReady) ?_
    remaining state ready fuel allowCoins
  intro residual current currentReady extra coins
  exact cap_open_record_execute
    (cap_open_records_entry context records reference current residual
      indexSpace outputSpace heapBelow saltsBelow inputs currentReady) extra coins

theorem cap_open_records_loop_finished (context : CapOpenRecordContext)
    (records : List Index) (reference : MachineState)
    (countBound : records.length < 2^64)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (outputSpace : context.output+576*records.length ≤ context.limit)
    (heapBelow : context.roots+2147483648 ≤ context.output)
    (saltsBelow : context.salts+536870912 ≤ context.output)
    (inputs : CapOpenRecordInputs context records reference)
    (remaining : Nat) (state : MachineState)
    (ready : CapOpenRecordsReady context records reference remaining state) :
    CapOpenRecordsReady context records reference 0
      (capCountedRun capOpenRecordState remaining state) := by
  exact cap_counted_run_ready capOpenRecordState (CapOpenRecordsReady context records reference)
    (fun residual current currentReady =>
      cap_open_records_ready_next context records reference current residual
        countBound indexSpace outputSpace heapBelow saltsBelow inputs currentReady)
    remaining state ready

end CommitGolfCandidate
