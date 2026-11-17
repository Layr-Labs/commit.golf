import CommitGolfCandidate.Group341Encoding
import CommitGolf.Statements

/-! Proved static properties of the baseline images. Execution and security properties
must still be established before constructing CommitGolf.Certificate. -/
namespace CommitGolfCandidate
open CommitGolf

private theorem image_valid_of_lengths (image : Riscv.Image)
    (buffers : List (Nat × Nat)) (codeCount dataCount : Nat)
    (codeLength : image.code.length=codeCount) (dataLength : image.data.length=dataCount)
    (small : 4*codeCount+dataCount<Riscv.MAX_PROGRAM_BYTES)
    (layout : (∀ buffer∈buffers,
      buffer.1%8=0 ∧ buffer.1+buffer.2≤16*((Riscv.MEMORY_BYTES-dataCount)/16)) ∧
      buffers.Pairwise Riscv.DisjointBuffers) : image.Valid buffers := by
  change (4*image.code.length+image.data.length<Riscv.MAX_PROGRAM_BYTES) ∧
    ((∀ buffer∈buffers,
      buffer.1%8=0 ∧ buffer.1+buffer.2≤16*((Riscv.MEMORY_BYTES-image.data.length)/16)) ∧
      buffers.Pairwise Riscv.DisjointBuffers)
  rw [codeLength,dataLength]
  exact ⟨small,layout⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Admission uses proved image lengths, avoiding materialization of the large code list. -/
theorem submission_admission : submission.Admission := by
  intro program
  cases program with
  | commit =>
    refine ⟨?_,by decide,by decide⟩
    apply image_valid_of_lengths _ _ 253816 0
    · change group341ImageWords.length=253816
      exact group341_image_length
    · rfl
    · decide
    · norm_num [submission,candidate,layout,sizes,trapdoorBytes,openingBytes,Layout.buffers,Riscv.DisjointBuffers,
        Riscv.MEMORY_BYTES,LENGTH,LOG_LENGTH,LEAF_SIZE,DIGEST_BYTES]
  | opening => decide
  | check => decide

theorem batch_proof_bytes : BATCH * openingBytes LOG_LENGTH = 102400 := by
  norm_num [BATCH, openingBytes, LOG_LENGTH]

/-- Eight leaf calls and one internal-node call per leaf, except at the root. -/
theorem commit_queries_fit : 9 * LENGTH - 1 ≤ COMMIT_BUDGET := by
  norm_num [LENGTH, LOG_LENGTH, COMMIT_BUDGET]

theorem check_queries_fit (positions : Nat) :
    (8 + LOG_LENGTH) * positions ≤ CHECK_BUDGET positions := by
  simp only [LOG_LENGTH, CHECK_BUDGET]
  omega

end CommitGolfCandidate
