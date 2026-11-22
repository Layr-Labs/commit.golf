import CommitGolfCandidate.GroupOpenCapPreparation
import CommitGolfCandidate.GroupOpenCapEmit
import CommitGolfCandidate.GroupOpenExit

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Opening (markBase trapdoorBase markMachine markParentPrefix mark_addresses parentAddress
  marks_before_trapdoor nat_address_injective)

attribute [local irreducible] execute

theorem cap_preparation_frame (state : MachineState) (address : Nat) (above : Opening.trapdoorBase ≤ address)
    (fit : address < 2^64) (base : state.getReg .x26 = BitVec.ofNat 64 markBase) :
    (capPreparation state).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  clear base
  exact CapStudy.cap_preparation_frame state address above fit

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

@[local simp] private theorem abi_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

/-- The return block at 709 (reached from the root exit `jal` at 705): four cycles including the halt. -/
theorem root_exit (state : MachineState) (pc : state.pc = 0x1b14) (fuel : Nat) (allowCoins : Bool) :
    let result := exitPrefix state 3
    execute openingImage (4 + fuel) state allowCoins = pure ⟨.success, result, 4, 0⟩ ∧
    result.mem = state.mem ∧ result.getReg .x11 = state.getReg .x21 - state.getReg .x20 :=
  ⟨execute_exit state pc fuel allowCoins, exit_memory state, exit_register state⟩

theorem terminal_length (state : MachineState) (outputLen : Nat)
    (final : state.getReg .x21 = BitVec.ofNat 64 (quartetProofBase+outputLen))
    (start : state.getReg .x20 = BitVec.ofNat 64 quartetProofBase)
    (fits : quartetProofBase + outputLen ≤ MEMORY_BYTES) :
    (state.getReg .x21 - state.getReg .x20).toNat = outputLen := by
  rw [final, start, BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by
    have : quartetProofBase < 2^64 := by decide
    omega) (by omega), Nat.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  unfold MEMORY_BYTES at fits
  omega

end TwoPermutationPrototype.GroupedOpening
