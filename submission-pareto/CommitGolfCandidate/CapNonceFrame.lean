import CommitGolfCandidate.CapNonceCopy
import CommitGolfCandidate.CapOpenRetainedInputs

/-! The salt-field block writes only inside the admitted output window. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
theorem cap_open_retained_nonce (floor cursor : Nat) (state reference : MachineState)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 cursor)
    (aligned : cursor % 8 = 0) (cursorBound : cursor+32 ≤ 2^64)
    (before : floor ≤ cursor) (frame : CapOpenRetainedInputs floor reference state) :
    CapOpenRetainedInputs floor reference (capNonceEightState state) := by
  intro address high below
  rw [cap_nonce_byte_outside state cursor address pointer aligned cursorBound
    (by omega) (Or.inl (by omega))]
  exact frame address high below

end CommitGolfCandidate
