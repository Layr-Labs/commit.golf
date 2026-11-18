import CommitGolfCandidate.NonceCompactPacked
import CommitGolfCandidate.NonceOldOpeningReady

/-! The delivered opener's run: the cap-level opener's run, the jump at word 110, and the
compaction of its internal proof. Cycles add up exactly; no oracle call. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

/-- The state that enters the compaction (word 192). -/
def nonceCodecEntry (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    MachineState :=
  (nonceOldOpeningResult trapdoor positions).state.setPC 4864

theorem nonce_codec_exists (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    ∃ final, (∀ fuel coins, execute s6OpeningImage
        (nonceCodecCycles positions.card (nonceOldFooterNodes trapdoor positions) + fuel)
        (nonceCodecEntry trapdoor positions) coins =
          pure ⟨.success, final, nonceCodecCycles positions.card (nonceOldFooterNodes trapdoor positions), 0⟩) ∧
      (final.getReg .x11).toNat = 560 * positions.card + 32 * nonceOldFooterNodes trapdoor positions ∧
      NonceCompacted (nonceCodecEntry trapdoor positions) capProgram.layout.proof positions.card
        (560 * positions.card + 32 * nonceOldFooterNodes trapdoor positions) final := by
  have inputs := nonce_old_opening_ready trapdoor positions
  exact s6_compact_run (nonceCodecEntry trapdoor positions) capProgram.layout.proof positions.card
    (nonceOldFooterNodes trapdoor positions) rfl (MachineState.getReg_setPC.trans inputs.1)
    (MachineState.getReg_setPC.trans inputs.2.1) (MachineState.getReg_setPC.trans inputs.2.2)
    nonce_old_proof_aligned (nonce_old_memory_window trapdoor positions)

noncomputable def nonceCodecFinalState (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : MachineState :=
  Classical.choose (nonce_codec_exists trapdoor positions)

noncomputable def nonceCodecResult (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : Execution :=
  ⟨.success, nonceCodecFinalState trapdoor positions,
    nonceCodecCycles positions.card (nonceOldFooterNodes trapdoor positions), 0⟩

theorem nonce_codec_loaded_execute (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) (fuel : Nat) :
    execute s6OpeningImage (nonceCodecCycles positions.card (nonceOldFooterNodes trapdoor positions) + fuel)
      (nonceCodecEntry trapdoor positions) true = pure (nonceCodecResult trapdoor positions) :=
  (Classical.choose_spec (nonce_codec_exists trapdoor positions)).1 fuel true

theorem nonce_codec_report (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    ((nonceCodecFinalState trapdoor positions).getReg .x11).toNat =
      560 * positions.card + 32 * nonceOldFooterNodes trapdoor positions :=
  (Classical.choose_spec (nonce_codec_exists trapdoor positions)).2.1

theorem nonce_codec_bytes (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    NonceCompacted (nonceCodecEntry trapdoor positions) capProgram.layout.proof positions.card
      (560 * positions.card + 32 * nonceOldFooterNodes trapdoor positions)
      (nonceCodecFinalState trapdoor positions) :=
  (Classical.choose_spec (nonce_codec_exists trapdoor positions)).2.2

theorem nonce_codec_fuel_bound (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    nonceCodecCycles positions.card (nonceOldFooterNodes trapdoor positions) ≤
      2 * capProgram.steps .opening - nonceOldOpeningSteps positions := by
  have cardinal := nonce_old_count_bound positions
  have footer := nonce_old_footer_bound trapdoor positions
  have steps := nonce_old_opening_steps_bound positions
  have total : capProgram.steps .opening = 13421773824 := rfl
  rw [total]
  unfold nonceCodecCycles
  omega

noncomputable def nonceCompressedOpeningResult (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : Execution :=
  (nonceCodecResult trapdoor positions).charge (nonceOldOpeningResult trapdoor positions).cycles 0

theorem nonce_compressed_opening_run (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    nonceCompressedProgram.run .opening (trapdoor,positions)=
      pure (nonceCompressedOpeningResult trapdoor positions) := by
  obtain ⟨extra, large, split⟩ := nonce_compressed_opening_split trapdoor positions
  have enough := (nonce_codec_fuel_bound trapdoor positions).trans large
  have execution := nonce_codec_loaded_execute trapdoor positions
    (extra - nonceCodecCycles positions.card (nonceOldFooterNodes trapdoor positions))
  rw [Nat.add_sub_of_le enough] at execution
  rw [split]
  unfold nonceCodecEntry at execution
  rw [execution, pure_bind]
  rfl

theorem nonce_compressed_result_report (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    ((nonceCompressedOpeningResult trapdoor positions).state.getReg .x11).toNat=
      560*positions.card+32*nonceOldFooterNodes trapdoor positions :=
  nonce_codec_report trapdoor positions

theorem nonce_compressed_result_calls (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : (nonceCompressedOpeningResult trapdoor positions).oracleCalls = 0 := rfl

theorem nonce_compressed_result_cycles (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    (nonceCompressedOpeningResult trapdoor positions).cycles =
      (nonceOldOpeningResult trapdoor positions).cycles +
        nonceCodecCycles positions.card (nonceOldFooterNodes trapdoor positions) := rfl

end CommitGolfCandidate
