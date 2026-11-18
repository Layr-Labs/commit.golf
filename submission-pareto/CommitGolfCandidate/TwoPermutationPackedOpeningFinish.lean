import CommitGolfCandidate.TwoPermutationPackedOpeningCapPreparation
import CommitGolfCandidate.TwoPermutationPackedOpeningCapEmit
import CommitGolfCandidate.TwoPermutationPackedOpeningExit

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Opening (markBase trapdoorBase proofBase markMachine markParentPrefix mark_addresses parentAddress
  marks_before_trapdoor nat_address_injective)

theorem cap_preparation_frame (state : MachineState) (address : Nat) (above : trapdoorBase ≤ address)
    (fit : address < 2^64) (base : state.getReg .x26 = BitVec.ofNat 64 markBase) :
    (capPreparation state).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  exact Opening.Postorder.frame (unrollEnter state) 1 8 0 address Opening.cap_span_root above fit

attribute [local simp] advance_code right_code up_code

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

@[local simp] private theorem abi_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

theorem root_exit (state : MachineState) (pc : state.pc = 0x1a74)
    (root : state.getReg .x6 = 1#64) (fuel : Nat) (allowCoins : Bool) :
    let result := exitPrefix (advanceUp state) 3
    execute openingImage (8 + fuel) state allowCoins = pure ⟨.success, result, 8, 0⟩ ∧
    result.mem = state.mem ∧ result.getReg .x11 = state.getReg .x21 - state.getReg .x20 := by
  let tested := afterAdvanceChecks state
  let checked := advanceUp state
  have odd : tested.pc = 0x1a8c := by
    rw [show tested.pc = _ from advance_parity_target state pc, root]; rfl
  have testNode : tested.getReg .x6 = 1#64 := by
    simp [tested, afterAdvanceChecks, advancePrefix, advanceCode, execInstrBr, signExtend12, root]
  have ready : checked.pc = 0x1a94 := by
    rw [show checked.pc = _ from (advance_up_post tested odd).1, testNode]; rfl
  have memory : checked.mem = state.mem := by
    simp [checked, advanceUp, afterAdvanceChecks, advancePrefix, advanceCode, execInstrBr,
      signExtend12, root]
    rfl
  have dest : checked.getReg .x21 = state.getReg .x21 := by
    simp [checked, advanceUp, afterAdvanceChecks, advancePrefix, advanceCode, execInstrBr, signExtend12, root]
  have start : checked.getReg .x20 = state.getReg .x20 := by
    simp [checked, advanceUp, afterAdvanceChecks, advancePrefix, advanceCode, execInstrBr, signExtend12, root]
  refine ⟨?_, (exit_memory checked).trans memory, ?_⟩
  · rw [show 8 + fuel = 2 + (2 + (4 + fuel)) by omega, execute_advance_parity_test _ pc,
      execute_advance_up (advancePrefix state 41 2) odd,
      execute_exit (advancePrefix (advancePrefix state 41 2) 47 2) ready]
    simp [Execution.charge, advanceUp, afterAdvanceChecks]
  · rw [exit_register, dest, start]

theorem terminal_length (state : MachineState) (outputLen : Nat)
    (final : state.getReg .x21 = BitVec.ofNat 64 (proofBase+outputLen))
    (start : state.getReg .x20 = BitVec.ofNat 64 proofBase)
    (fits : proofBase + outputLen ≤ MEMORY_BYTES) :
    (state.getReg .x21 - state.getReg .x20).toNat = outputLen := by
  rw [final, start, BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by
    have : proofBase < 2^64 := by decide
    omega) (by omega), Nat.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  unfold MEMORY_BYTES at fits
  omega

end TwoPermutationPrototype.PackedOpening
