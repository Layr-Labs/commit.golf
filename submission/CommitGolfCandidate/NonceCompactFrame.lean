import CommitGolfCandidate.NonceCompactOuter

/-! Stable registers of the real record pass. In particular, x15 retains the
proof base and x22 the saved original proof end through every copy and return. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem nonce_compact_outer_register (state : MachineState) (count : Nat) (reg : Reg)
    (outside : reg ≠ .x1 ∧ reg ≠ .x6 ∧ reg ≠ .x23 ∧ reg ≠ .x24 ∧ reg ≠ .x25 ∧ reg ≠ .x28) :
    (capCountedRun nonceCompactRecordState count state).getReg reg=state.getReg reg := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    rw [capCountedRun, ih, nonce_compact_record_register state reg outside]

end CommitGolfCandidate
