import CommitGolfCandidate.CapOpenRecordsLoop

/-! Outside-register frame of the actual counted record pass. In particular
the original proof base x15 and cap leaf count x29 reach the mark/DFS phases
unchanged, without adding unnecessary fields to the runtime readiness state. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordState

theorem cap_open_records_register (context : CapOpenRecordContext)
    (records : List Index) (reference : MachineState)
    (countBound : records.length < 2^64)
    (indexSpace : context.indices+8*records.length+32 ≤ context.output)
    (outputSpace : context.output+576*records.length ≤ context.limit)
    (heapBelow : context.roots+2147483648 ≤ context.output)
    (saltsBelow : context.salts+536870912 ≤ context.output)
    (inputs : CapOpenRecordInputs context records reference)
    (remaining : Nat) (state : MachineState)
    (ready : CapOpenRecordsReady context records reference remaining state)
    (reg : Reg)
    (outside : reg ≠ .x1 ∧ reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23 ∧ reg ≠ .x30 ∧
      reg ≠ .x25 ∧ reg ≠ .x20 ∧ reg ≠ .x28 ∧
      reg ≠ .x24 ∧ reg ≠ .x27) :
    (capCountedRun capOpenRecordState remaining state).getReg reg =
      state.getReg reg := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
    rw [capCountedRun.eq_2, ih _ (cap_open_records_ready_next context records reference state
      remaining countBound indexSpace outputSpace heapBelow saltsBelow inputs ready)]
    exact cap_open_record_register state reg outside
      (cap_open_records_entry context records reference state remaining
        indexSpace outputSpace heapBelow saltsBelow inputs ready)

end CommitGolfCandidate
