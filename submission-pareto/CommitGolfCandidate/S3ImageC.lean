import CommitGolfCandidate.S3ImageB

/-! Instruction fetches of the appended code, part C: the decoded words of leaves 43..63, all leaves together, and
the leaf fetch lemma. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- Leaves 43..63 of `s3_leaf_decoded`. -/
theorem s3_leaf_decoded_third (l i : Nat) (low : 43 ≤ l) (hl : l < 64) (hi : i < 11) :
    (s3AppendedWords[218 + 11 * l + i]?).bind decodeInstruction =
      some (.base (((s3LeafCode l)[i]?).getD .EBREAK)) := by
  interval_cases l <;> interval_cases i <;> rfl

theorem s3_leaf_decoded (l i : Nat) (hl : l < 64) (hi : i < 11) :
    (s3AppendedWords[218 + 11 * l + i]?).bind decodeInstruction =
      some (.base (((s3LeafCode l)[i]?).getD .EBREAK)) := by
  by_cases first : l < 22
  · exact s3_leaf_decoded_first l i first hi
  · by_cases second : l < 43
    · exact s3_leaf_decoded_second l i (by omega) second hi
    · exact s3_leaf_decoded_third l i (by omega) hl hi

theorem s3_image_leaf (l i : Nat) (hl : l < 64) (hi : i < 11) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (1012276 + 44 * l + 4 * i)) :
    fetch (submission.image .commit) state =
      some (.base (((s3LeafCode l)[i]?).getD .EBREAK)) := by
  apply s3_image_word (218 + 11 * l + i) _ state (by omega) _ (s3_leaf_decoded l i hl hi)
  rw [pc]
  congr 1
  omega

end CommitGolfCandidate
