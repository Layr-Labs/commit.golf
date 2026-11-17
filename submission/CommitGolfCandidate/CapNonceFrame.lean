import CommitGolfCandidate.CapNonceCopy
import CommitGolfCandidate.CapOpenRetainedInputs

/-! The padded nonce copy writes exactly the same admitted output window. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
theorem cap_nonce_byte_outside (state : MachineState)
    (destination address : Nat)
    (pointer : state.getReg .x25 = BitVec.ofNat 64 destination)
    (aligned : destination % 8 = 0)
    (destinationBound : destination + 32 ≤ 2^64) (addressBound : address < 2^64)
    (outside : address < destination ∨ destination + 32 ≤ address) :
    (capNonceEightState state).getByte (BitVec.ofNat 64 address) =
      state.getByte (BitVec.ofNat 64 address) := by
  have decomposition : 8 * (address / 8) + address % 8 = address := by omega
  have memory :
      (capNonceEightState state).getMem
          (BitVec.ofNat 64 (8 * (address / 8))) =
        state.getMem (BitVec.ofNat 64 (8 * (address / 8))) := by
    apply cap_nonce_eight_memory_outside
    intro word equal
    rw [pointer, ← BitVec.ofNat_add] at equal
    have numeric := congrArg BitVec.toNat equal
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 8 * (address / 8) < 2^64),
      Nat.mod_eq_of_lt (by omega : destination + 8 * word.val < 2^64)] at numeric
    omega
  conv_lhs => rw [← decomposition]
  conv_rhs => rw [← decomposition]
  rw [aligned_byte _ (address / 8) (address % 8) (by omega),
    aligned_byte _ (address / 8) (address % 8) (by omega)]
  simp only [Nat.div_eq_of_lt (by omega : address % 8 < 8), Nat.mul_zero,
    Nat.add_zero, Nat.mod_eq_of_lt (by omega : address % 8 < 8), memory]

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
