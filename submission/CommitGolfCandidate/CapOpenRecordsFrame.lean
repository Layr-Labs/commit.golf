import CommitGolfCandidate.CapOpenRecordsLoop

/-! Outside-register frame of the actual counted record pass. In particular
the original proof base x15 and cap leaf count x29 reach the mark/DFS phases
unchanged, without adding unnecessary fields to the runtime readiness state. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capOpenRecordState

theorem cap_open_records_register (remaining : Nat) (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x23 ∧
      reg ≠ .x25 ∧ reg ≠ .x20 ∧ reg ≠ .x28 ∧
      reg ≠ .x24 ∧ reg ≠ .x27) :
    (capCountedRun capOpenRecordState remaining state).getReg reg =
      state.getReg reg := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
    rw [capCountedRun.eq_2, ih]
    exact cap_open_record_register state reg outside

end CommitGolfCandidate
