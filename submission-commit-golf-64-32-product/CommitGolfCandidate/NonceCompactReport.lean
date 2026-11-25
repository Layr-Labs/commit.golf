import CommitGolfCandidate.NonceOpeningResult

/-! The compacting epilogue reports its actual final cursor displacement.
This derives the serialized output length from the executed copy pointers. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem nonce_compact_final_report (state : MachineState) (base count words : Nat)
    (pc : state.pc=4540) (small : count<2^64)
    (window : base+544*count+8*words ≤ MEMORY_BYTES) (aligned : base%8=0)
    (proofBase : state.getReg .x15=BitVec.ofNat 64 base)
    (counter : state.getReg .x16=BitVec.ofNat 64 count)
    (oldEnd : state.getReg .x25=BitVec.ofNat 64 (base+544*count+8*words)) :
    ((nonceCodecFinalState state count words).getReg .x11).toNat=536*count+8*words := by
  have ready:=nonce_compact_entry_ready base count state pc small (by omega) aligned proofBase counter
  have finished:=nonce_compact_outer_finished base count count (nonceCompactEntryState state) ready
  have saved:=nonce_compact_records_saved state count
  have prefixBase : (nonceCompactFooterPrefix (nonceCompactRecordsEnd state count) 3).getReg .x15=
      BitVec.ofNat 64 base := by
    rw [nonce_compact_footer_register _ .x15 (by decide)]
    exact saved.2.trans proofBase
  have noWrap : base+(536*count+8*words)<2^64 := by
    norm_num [MEMORY_BYTES] at window
    omega
  by_cases empty : words=0
  · rw [nonceCodecFinalState,if_pos empty]
    apply nonce_compact_exit_report _ base _ prefixBase ?_ noWrap
    rw [nonce_compact_footer_register _ .x25 (by decide),empty]
    simp only [Nat.mul_zero,Nat.add_zero]
    exact finished.2.2.1
  · have footerReady:=nonce_compact_footer_ready state base count words pc small (by omega)
      window aligned proofBase counter oldEnd
    have copied:=nonce_copy_returned_finished _ _ words _ footerReady
    rw [nonceCodecFinalState,if_neg empty]
    apply nonce_compact_exit_report _ base _ ?_ ?_ noWrap
    · rw [nonce_copy_returned_register _ _ .x15 (by decide),
        nonce_compact_footer_call_register _ .x15 (by decide)]
      exact prefixBase
    · simpa only [Nat.add_assoc] using copied.2.1

theorem nonce_compressed_result_report (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    ((nonceCompressedOpeningResult trapdoor positions).state.getReg .x11).toNat=
      536*positions.card+8*nonceOldFooterWords trapdoor positions := by
  have inputs:=nonce_old_opening_ready trapdoor positions
  exact nonce_compact_final_report ((nonceOldOpeningResult trapdoor positions).state.setPC 4540)
    capProgram.layout.proof positions.card (nonceOldFooterWords trapdoor positions) rfl
    (nonce_old_count_bound positions) (nonce_old_codec_window trapdoor positions)
    nonce_old_proof_aligned inputs.1 inputs.2.1 inputs.2.2

theorem nonce_compressed_report_capacity (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    536*positions.card+8*nonceOldFooterWords trapdoor positions ≤ nonceCompressedProgram.sizes.proof := by
  have space:=cap_open_abi_output_space positions
  have footer:=nonce_old_footer_bound trapdoor positions
  change 536*positions.card+8*nonceOldFooterWords trapdoor positions ≤ capProgram.sizes.proof
  omega

end CommitGolfCandidate
