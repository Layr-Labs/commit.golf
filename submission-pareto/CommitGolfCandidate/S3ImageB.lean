import CommitGolfCandidate.S3ImageA

/-! Instruction fetches of the appended code, part B: the decoded words of leaves 22..42. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- Leaves 22..42 of `s3_leaf_decoded`. -/
theorem s3_leaf_decoded_second (l i : Nat) (low : 22 ≤ l) (hl : l < 43) (hi : i < 11) :
    (s3AppendedWords[218 + 11 * l + i]?).bind decodeInstruction =
      some (.base (((s3LeafCode l)[i]?).getD .EBREAK)) := by
  interval_cases l <;> interval_cases i <;> rfl

end CommitGolfCandidate
