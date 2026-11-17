import CommitGolfCandidate.NonceCompactRun
import CommitGolfCandidate.NonceOldOpeningReady

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceCodecCycles (count words : Nat) : Nat :=
  if words=0 then 12+411*count else 14+411*count+6*words

def nonceCodecFinalState (state : MachineState) (count words : Nat) : MachineState :=
  if words=0 then nonceCompactExitState
    (nonceCompactFooterPrefix (nonceCompactRecordsEnd state count) 3)
  else nonceCompactExitState (nonceCopyReturned (nonceCompactFooterCall
    (nonceCompactFooterPrefix (nonceCompactRecordsEnd state count) 3)) words)

def nonceCodecResult (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : Execution :=
  ⟨.success, nonceCodecFinalState ((nonceOldOpeningResult trapdoor positions).state.setPC 4540)
      positions.card (nonceOldFooterWords trapdoor positions),
    nonceCodecCycles positions.card (nonceOldFooterWords trapdoor positions),0⟩

theorem nonce_codec_loaded_execute (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) (fuel : Nat) :
    execute nonceCompactImage
      (nonceCodecCycles positions.card (nonceOldFooterWords trapdoor positions)+fuel)
      ((nonceOldOpeningResult trapdoor positions).state.setPC 4540) true=
        pure (nonceCodecResult trapdoor positions) := by
  let state := (nonceOldOpeningResult trapdoor positions).state.setPC 4540
  have inputs:=nonce_old_opening_ready trapdoor positions
  have base : state.getReg .x15=BitVec.ofNat 64 capProgram.layout.proof := inputs.1
  have count : state.getReg .x16=BitVec.ofNat 64 positions.card := inputs.2.1
  have oldEnd : state.getReg .x25=BitVec.ofNat 64
      (capProgram.layout.proof+544*positions.card+8*nonceOldFooterWords trapdoor positions) := inputs.2.2
  have window:=nonce_old_codec_window trapdoor positions
  by_cases empty : nonceOldFooterWords trapdoor positions=0
  · rw [empty, Nat.mul_zero, Nat.add_zero] at oldEnd window
    unfold nonceCodecResult nonceCodecFinalState nonceCodecCycles
    simp only [if_pos empty]
    exact nonce_compact_run_empty_footer state capProgram.layout.proof positions.card rfl
      (nonce_old_count_bound positions) window nonce_old_proof_aligned base count oldEnd fuel true
  · unfold nonceCodecResult nonceCodecFinalState nonceCodecCycles
    simp only [if_neg empty]
    exact nonce_compact_run_positive_footer state capProgram.layout.proof positions.card
      (nonceOldFooterWords trapdoor positions) rfl (nonce_old_count_bound positions) (by omega)
      window nonce_old_proof_aligned base count oldEnd fuel true

theorem nonce_codec_fuel_bound (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    nonceCodecCycles positions.card (nonceOldFooterWords trapdoor positions) ≤ capProgram.steps .opening := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  have footer:=nonce_old_footer_bound trapdoor positions
  norm_num [LENGTH, LOG_LENGTH] at cardinal
  change nonceCodecCycles positions.card (nonceOldFooterWords trapdoor positions) ≤ 13421773824
  unfold nonceCodecCycles
  split <;> omega

def nonceCompressedOpeningResult (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : Execution :=
  (nonceCodecResult trapdoor positions).charge (nonceOldOpeningResult trapdoor positions).cycles 0

theorem nonce_compressed_opening_run (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    nonceCompressedProgram.run .opening (trapdoor,positions)=
      pure (nonceCompressedOpeningResult trapdoor positions) := by
  obtain ⟨extra,large,split⟩:=nonce_compressed_opening_split trapdoor positions
  have enough : nonceCodecCycles positions.card (nonceOldFooterWords trapdoor positions) ≤ extra :=
    (nonce_codec_fuel_bound trapdoor positions).trans large
  have execution:=nonce_codec_loaded_execute trapdoor positions
    (extra-nonceCodecCycles positions.card (nonceOldFooterWords trapdoor positions))
  rw [Nat.add_sub_of_le enough] at execution
  rw [split,execution]
  rfl

end CommitGolfCandidate
