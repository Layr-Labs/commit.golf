import CommitGolfCandidate.Layout2Blocks
import CommitGolfCandidate.TwoPermutationPackedImage

namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.Packed.Checker

set_option maxRecDepth 14000
set_option maxHeartbeats 1200000

theorem concrete_program : Program packedImage := by
  intro b
  cases b <;> intro j <;> fin_cases j <;> rfl

theorem delivered_image : K1Artifact.submission.image .check=packedImage := rfl

end CommitGolfCandidate.Layout2
