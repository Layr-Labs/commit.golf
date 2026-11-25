import CommitGolfCandidate.Check
import CommitGolfCandidate.MemoryCore

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- The compression reply is read back as the identical 256-bit digest. -/
theorem check_compression_digest (state : MachineState) (answer : BitVec 256) :
    readBuffer (checkCompressionState state answer) 256 32 = answer := by
  rw [read_digest_words _ _ (by decide)]
  have w0 := check_compression_word state answer 0 (by decide)
  have w1 := check_compression_word state answer 1 (by decide)
  have w2 := check_compression_word state answer 2 (by decide)
  have w3 := check_compression_word state answer 3 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at w0 w1 w2 w3
  rw [w0, w1, w2, w3]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide),
    BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  simp

end CommitGolfCandidate
