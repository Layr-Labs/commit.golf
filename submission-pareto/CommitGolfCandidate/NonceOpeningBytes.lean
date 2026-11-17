import CommitGolfCandidate.NonceActualCompactMemory
import CommitGolfCandidate.NonceCompactBytes
import CommitGolfCandidate.NonceCompactReport

/-! The concrete opener's emitted proof is exactly a deterministic compaction
of the retained opener's emitted proof, for every admitted loaded input.
Both reported lengths and successful readProof branches come from execution. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
attribute [local irreducible] nonceCodecFinalState capOpenFinalState capOpenInitializedState

theorem nonce_old_result_report (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    ((nonceOldOpeningResult trapdoor positions).state.getReg .x11).toNat=
      544*positions.card+8*nonceOldFooterWords trapdoor positions := by
  by_cases empty : positions.card=0
  · have resultEq : nonceOldOpeningResult trapdoor positions=capOpenEmptyResult trapdoor positions := by
      unfold nonceOldOpeningResult
      exact if_pos empty
    have lengthEq : 544*positions.card+8*nonceOldFooterWords trapdoor positions=0 := by
      unfold nonceOldFooterWords
      rw [if_pos empty,empty]
    rw [resultEq,lengthEq]
    unfold capOpenEmptyResult
    rw [cap_open_empty_report]
    rfl
  · have resultEq : nonceOldOpeningResult trapdoor positions=capOpenNonemptyResult trapdoor positions := by
      unfold nonceOldOpeningResult
      exact if_neg empty
    rw [resultEq,cap_open_nonempty_result_length trapdoor positions (by omega),
      cap_open_loaded_bytes_length,nonceOldFooterWords,if_neg empty]
    omega

theorem nonce_old_result_succeeded (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : capProgram.openingSucceeded (nonceOldOpeningResult trapdoor positions)=true := by
  have space:=cap_open_abi_output_space positions
  have footer:=nonce_old_footer_bound trapdoor positions
  have capacity : 544*positions.card+8*nonceOldFooterWords trapdoor positions ≤ capProgram.sizes.proof := by omega
  rw [Submission.openingSucceeded,nonce_old_opening_success,nonce_old_result_report]
  change decide (544*positions.card+8*nonceOldFooterWords trapdoor positions ≤ capProgram.sizes.proof)=true
  simpa only [decide_eq_true_eq] using capacity

theorem nonce_compressed_result_succeeded (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    nonceCompressedProgram.openingSucceeded (nonceCompressedOpeningResult trapdoor positions)=true := by
  have success : (nonceCompressedOpeningResult trapdoor positions).exit=.success := rfl
  rw [Submission.openingSucceeded,success,nonce_compressed_result_report]
  change decide (536*positions.card+8*nonceOldFooterWords trapdoor positions ≤ nonceCompressedProgram.sizes.proof)=true
  simpa only [decide_eq_true_eq] using nonce_compressed_report_capacity trapdoor positions

theorem nonce_old_result_read_proof (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    capProgram.readProof (nonceOldOpeningResult trapdoor positions)=
      nonceMemoryBytes (nonceOldOpeningResult trapdoor positions).state capProgram.layout.proof
        (544*positions.card+8*nonceOldFooterWords trapdoor positions) := by
  simp only [Submission.readProof,nonce_old_result_succeeded,↓reduceIte,
    nonce_old_result_report,nonceMemoryBytes]

theorem nonce_compressed_result_read_proof (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    nonceCompressedProgram.readProof (nonceCompressedOpeningResult trapdoor positions)=
      nonceMemoryBytes (nonceCompressedOpeningResult trapdoor positions).state capProgram.layout.proof
        (536*positions.card+8*nonceOldFooterWords trapdoor positions) := by
  simp only [Submission.readProof,nonce_compressed_result_succeeded,↓reduceIte,
    nonce_compressed_result_report,nonceMemoryBytes] <;> rfl

theorem nonce_opening_proof_compaction (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    nonceCompressedProgram.readProof (nonceCompressedOpeningResult trapdoor positions)=
      NonceCodec.compact positions.card (capProgram.readProof (nonceOldOpeningResult trapdoor positions)) := by
  have inputs:=nonce_old_opening_ready trapdoor positions
  have effect:=nonce_compact_complete_memory ((nonceOldOpeningResult trapdoor positions).state.setPC 4540)
    capProgram.layout.proof positions.card (nonceOldFooterWords trapdoor positions) rfl
    (nonce_old_count_bound positions) (nonce_old_codec_window trapdoor positions)
    nonce_old_proof_aligned inputs.1 inputs.2.1 inputs.2.2
  have bytes:=nonce_compact_memory_bytes capProgram.layout.proof positions.card
    (nonceOldFooterWords trapdoor positions) _ _ nonce_old_proof_aligned effect
  rw [nonce_compressed_result_read_proof,nonce_old_result_read_proof]
  exact bytes

end CommitGolfCandidate
