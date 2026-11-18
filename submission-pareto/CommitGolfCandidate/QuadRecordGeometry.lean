import CommitGolfCandidate.QuadCheckRecordData

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64

def ProofWithin (input : CheckInput) : Prop :=
  606*input.positions.card≤ input.proof.length ∧ input.proof.length≤606*2^24+7680

theorem quad_record_geometry (input : CheckInput) (ordinal : Nat)
    (present : ordinal< input.positions.card) (fits : ProofWithin input) :
    checkProofByte ordinal%2=0 ∧
      checkProofByte ordinal+606≤11190423648+input.proof.length ∧
      32768≤checkProofByte ordinal ∧ checkProofByte ordinal+606≤MEMORY_BYTES ∧
      checkSourceWord ordinal+37≤2^33 := by
  have count := checker_positions_bound input
  obtain ⟨atLeast,atMost⟩ := fits
  unfold checkProofByte checkSourceWord MEMORY_BYTES
  omega

end TwoPermutationPrototype.Quad.Checker
