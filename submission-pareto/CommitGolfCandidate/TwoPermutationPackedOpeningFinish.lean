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

/-- The root's advance reaches the common exit block; the pack postpass then rewrites the
unpacked proof (`k` records, `b` footer digests at `proofBase`) into `ProofCodec.HeadStreamFour.pack` and halts. -/
theorem root_exit (state : MachineState) (pc : state.pc = 0x1a3c)
    (root : state.getReg .x6 = 1#64) (k b : Nat)
    (count : state.getReg .x16 = BitVec.ofNat 64 k)
    (start : state.getReg .x20 = BitVec.ofNat 64 proofBase)
    (length : state.getReg .x21 - state.getReg .x20 = BitVec.ofNat 64 (498*k + 30*b))
    (fits : 498*k + 30*b ≤ Pack.capacityBytes) :
    ∃ final : MachineState,
      (∀ fuel allowCoins, execute openingImage (4 + HeadStream.exitSteps k b + fuel) state allowCoins =
        pure ⟨.success, final, 4 + HeadStream.exitCycles k b, 0⟩) ∧
      (final.getReg .x11).toNat = ProofCodec.HeadStreamFour.packedLength k (15*k + b) ∧
      (∀ p < ProofCodec.HeadStreamFour.packedLength k (15*k + b),
        final.getByte (BitVec.ofNat 64 (proofBase + p)) =
          (ProofCodec.HeadStreamFour.pack k (proofBytes state (498*k + 30*b))).getD p 0) ∧
      (∀ a : Word, a.toNat < proofBase ∨ proofBase + 2^34 ≤ a.toNat →
        final.getByte a = state.getByte a) := by
  let tested := afterAdvanceChecks state
  let checked := advanceUp state
  have odd : tested.pc = 0x1a54 := by
    rw [show tested.pc = _ from advance_parity_target state pc, root]; rfl
  have testNode : tested.getReg .x6 = 1#64 := by
    simp [tested, afterAdvanceChecks, advancePrefix, advanceCode, execInstrBr, signExtend12, root]
  have ready : checked.pc = 0x1a5c := by
    rw [show checked.pc = _ from (advance_up_post tested odd).1, testNode]; rfl
  have memory : checked.mem = state.mem := by
    simp [checked, advanceUp, afterAdvanceChecks, advancePrefix, advanceCode, execInstrBr,
      signExtend12, root]
    rfl
  have dest : checked.getReg .x21 = state.getReg .x21 := by
    simp [checked, advanceUp, afterAdvanceChecks, advancePrefix, advanceCode, execInstrBr, signExtend12, root]
  have begin : checked.getReg .x20 = state.getReg .x20 := by
    simp [checked, advanceUp, afterAdvanceChecks, advancePrefix, advanceCode, execInstrBr, signExtend12, root]
  have counted : checked.getReg .x16 = state.getReg .x16 := by
    simp [checked, advanceUp, afterAdvanceChecks, advancePrefix, advanceCode, execInstrBr, signExtend12, root]
  obtain ⟨final, ran, ret, bytes, frame⟩ := execute_exit checked ready k b (counted.trans count)
    (begin.trans start) (by rw [dest, begin]; exact length) fits
  refine ⟨final, fun fuel allowCoins => ?_, ret, ?_, ?_⟩
  · rw [show 4 + HeadStream.exitSteps k b + fuel = 2 + (2 + (HeadStream.exitSteps k b + fuel)) by omega,
      execute_advance_parity_test _ pc, execute_advance_up (advancePrefix state 41 2) odd]
    have ran' : execute openingImage (HeadStream.exitSteps k b + fuel) (advancePrefix (advancePrefix state 41 2) 47 2)
        allowCoins = pure ⟨.success, final, HeadStream.exitCycles k b, 0⟩ := ran fuel allowCoins
    rw [ran']
    simp only [pure_bind, Execution.charge]
    congr 2
    omega
  · intro p inside
    rw [bytes p inside, proof_bytes_congr memory]
  · intro a outside
    rw [frame a outside]
    simp only [MachineState.getByte, MachineState.getMem, memory]

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
