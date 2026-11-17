import CommitGolfCandidate.NonceCompactOuter

/-! Stable registers of the real record pass. In particular, x15 retains the
proof base and x22 the saved original proof end through every copy and return. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem nonce_compact_record_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x1 ∧ reg ≠ .x6 ∧ reg ≠ .x23 ∧ reg ≠ .x24 ∧ reg ≠ .x25 ∧ reg ≠ .x28) :
    (nonceCompactRecordState state).getReg reg=state.getReg reg := by
  rw [nonceCompactRecordState, nonce_compact_tail_register _ reg outside.2.2.2.1]
  rw [nonceCompactSiblingsCopied,
    nonce_copy_returned_register _ _ reg ⟨outside.2.1,outside.2.2.1,outside.2.2.2.2.1,outside.2.2.2.2.2⟩]
  change (nonceCompactCallPrefix true (nonceCompactNonceCopied state)
    (nonceCompactCallCount true)).getReg reg=_
  rw [nonce_compact_call_register true _ reg ⟨outside.1,outside.2.2.1,outside.2.2.2.2.2⟩]
  rw [nonceCompactNonceCopied,
    nonce_copy_returned_register _ _ reg ⟨outside.2.1,outside.2.2.1,outside.2.2.2.2.1,outside.2.2.2.2.2⟩]
  change (nonceCompactCallPrefix false state (nonceCompactCallCount false)).getReg reg=_
  exact nonce_compact_call_register false state reg ⟨outside.1,outside.2.2.1,outside.2.2.2.2.2⟩

theorem nonce_compact_outer_register (state : MachineState) (count : Nat) (reg : Reg)
    (outside : reg ≠ .x1 ∧ reg ≠ .x6 ∧ reg ≠ .x23 ∧ reg ≠ .x24 ∧ reg ≠ .x25 ∧ reg ≠ .x28) :
    (capCountedRun nonceCompactRecordState count state).getReg reg=state.getReg reg := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    rw [capCountedRun, ih, nonce_compact_record_register state reg outside]

end CommitGolfCandidate
