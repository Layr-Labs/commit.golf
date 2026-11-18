import CommitGolfCandidate.CapCheckPathTail
import CommitGolfCandidate.CapExperimentalABI
import CommitGolfCandidate.CapMarkImage

/-! Actual lower-path compression and latch bytes in the experimental checker.
The preparation branch has separate fetch proofs; these link the common
compression and the seven-instruction latch (with its truncation code) without
borrowing old-image facts. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

theorem cap_check_path_compression_fetched :
    CapCheckCompressionFetched ((capExperimental 24).image .check) 4380 := by
  constructor
  · intro state i bounded pc
    apply cap_image_fetch _ (capCheckCompressionPrefix state i) (71+i) _ (by omega)
    · rw [cap_check_compression_prefix_pc state i (by omega), pc]
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · intro state pc
    apply cap_image_fetch _ (capCheckCompressionPrefix state 5) 76 _ (by decide)
    · rw [cap_check_compression_prefix_pc state 5 (by decide), pc]
      rfl
    · rfl

theorem cap_check_path_tail_fetched :
    CapCheckPathTailFetched ((capExperimental 24).image .check) := by
  intro state i bounded pc
  apply cap_image_fetch _ (capCheckPathTailPrefix state i) (capCheckPathTailWord i) _
    (by interval_cases i <;> decide)
  · exact cap_check_path_tail_prefix_pc state i bounded pc
  · interval_cases i <;> rfl

end CommitGolfCandidate
