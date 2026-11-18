import CommitGolfCandidate.NonceOpeningResult

/-! The delivered proof is `s6Pack` of the cap-level opener's proof, for every admitted input.
Both reported lengths and both successful `readProof` branches come from execution. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
attribute [local irreducible] capOpenFinalState capOpenInitializedState

theorem nonce_old_result_report (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    ((nonceOldOpeningResult trapdoor positions).state.getReg .x11).toNat=
      576*positions.card+32*nonceOldFooterNodes trapdoor positions := by
  by_cases empty : positions.card=0
  · have resultEq : nonceOldOpeningResult trapdoor positions=capOpenEmptyResult trapdoor positions := by
      unfold nonceOldOpeningResult
      exact if_pos empty
    have lengthEq : 576*positions.card+32*nonceOldFooterNodes trapdoor positions=0 := by
      unfold nonceOldFooterNodes
      rw [if_pos empty,empty]
    rw [resultEq,lengthEq]
    unfold capOpenEmptyResult
    rw [cap_open_empty_report]
    rfl
  · have resultEq : nonceOldOpeningResult trapdoor positions=capOpenNonemptyResult trapdoor positions := by
      unfold nonceOldOpeningResult
      exact if_neg empty
    rw [resultEq,cap_open_nonempty_result_length trapdoor positions (by omega),
      cap_open_loaded_bytes_length,nonceOldFooterNodes,if_neg empty]

theorem nonce_old_result_succeeded (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) : capProgram.openingSucceeded (nonceOldOpeningResult trapdoor positions)=true := by
  have window:=nonce_old_codec_window trapdoor positions
  rw [Submission.openingSucceeded,nonce_old_opening_success,nonce_old_result_report]
  change decide (576*positions.card+32*nonceOldFooterNodes trapdoor positions ≤ capProgram.sizes.proof)=true
  simpa only [decide_eq_true_eq] using (by omega : 576*positions.card+32*nonceOldFooterNodes trapdoor positions ≤
    capProgram.sizes.proof)

theorem nonce_compressed_result_succeeded (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    nonceCompressedProgram.openingSucceeded (nonceCompressedOpeningResult trapdoor positions)=true := by
  have window:=nonce_old_codec_window trapdoor positions
  have success : (nonceCompressedOpeningResult trapdoor positions).exit=.success := rfl
  rw [Submission.openingSucceeded,success,nonce_compressed_result_report]
  change decide (534*positions.card+30*nonceOldFooterNodes trapdoor positions ≤ capProgram.sizes.proof)=true
  simpa only [decide_eq_true_eq] using (by omega : 534*positions.card+30*nonceOldFooterNodes trapdoor positions ≤
    capProgram.sizes.proof)

theorem nonce_old_result_read_proof (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    capProgram.readProof (nonceOldOpeningResult trapdoor positions)=
      nonceMemoryBytes (nonceOldOpeningResult trapdoor positions).state capProgram.layout.proof
        (576*positions.card+32*nonceOldFooterNodes trapdoor positions) := by
  simp only [Submission.readProof,nonce_old_result_succeeded,↓reduceIte,
    nonce_old_result_report,nonceMemoryBytes]

theorem nonce_compressed_result_read_proof (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    nonceCompressedProgram.readProof (nonceCompressedOpeningResult trapdoor positions)=
      nonceMemoryBytes (nonceCompressedOpeningResult trapdoor positions).state capProgram.layout.proof
        (534*positions.card+30*nonceOldFooterNodes trapdoor positions) := by
  simp only [Submission.readProof,nonce_compressed_result_succeeded,↓reduceIte,
    nonce_compressed_result_report,nonceMemoryBytes] <;> rfl

/-- The delivered proof is the packed cap-level proof. -/
theorem nonce_opening_proof_compaction (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    nonceCompressedProgram.readProof (nonceCompressedOpeningResult trapdoor positions)=
      s6Pack positions.card (capProgram.readProof (nonceOldOpeningResult trapdoor positions)) := by
  rw [nonce_compressed_result_read_proof,nonce_old_result_read_proof]
  exact nonce_compacted_bytes (nonceCodecEntry trapdoor positions) _ capProgram.layout.proof positions.card
    (nonceOldFooterNodes trapdoor positions) (nonce_codec_bytes trapdoor positions)

theorem nonce_compressed_result_length (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    (nonceCompressedProgram.readProof (nonceCompressedOpeningResult trapdoor positions)).length =
      534*positions.card+30*nonceOldFooterNodes trapdoor positions := by
  rw [nonce_compressed_result_read_proof, nonce_memory_bytes_length]

end CommitGolfCandidate
