import CommitGolfCandidate.TwoPermutationPackedCheckRecordData
import CommitGolfCandidate.K3CLowerFormat
import CommitGolfCandidate.K3T238ArmCodec

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (RecordInputFrame honestIndex)
open TwoPermutationPrototype.QuartetCertificate (honestCheckInput)
open TwoPermutationPrototype.PackedHonest (honestHeap honest_projected_node honest_projected238_node)
set_option maxRecDepth 8192

/-- The upper sibling the checker reads at loop level `level`: 32 bytes for `level ≤ 1`, a 240-bit node (30 bytes,
two zero top bytes) for `level ≤ 5`, a 238-bit node from the packed block for `level ≥ 6`. -/
def lowerWireSibling (state : MachineState) (ordinal level : Nat) : Digest :=
  if level ≤ 1 then readBuffer state (lowerProofByte ordinal level) 32
  else if level ≤ 5 then 0#16 ++ readBuffer state (lowerProofByte ordinal level) 30
  else packedSibling state ordinal level

/-- The sibling of the loop-level-`level` path node lies in the heap row `[2^(22-level), 2^(23-level))`. -/
theorem lower_sibling_range (index : Index) (level : Nat) (within : level < 14) :
    2^(22-level) ≤ Opening.lowerNode index (level+2) ^^^ 1 ∧
      Opening.lowerNode index (level+2) ^^^ 1 < 2^(23-level) := by
  have bounded := index.isLt
  change index.val < 16777216 at bounded
  have positive : 0 < 2^level := by positivity
  have low : 2^(22-level) * 2^level = 4194304 := by
    rw [← Nat.pow_add, show 22-level+level = 22 by omega]
  have high : 2^(23-level) * 2^level = 8388608 := by
    rw [← Nat.pow_add, show 23-level+level = 23 by omega]
  have twice : 2^(23-level) = 2*2^(22-level) := by
    rw [show 23-level = (22-level)+1 by omega, Nat.pow_succ, Nat.mul_comm]
  have even : 2^(22-level) = 2*2^(21-level) := by
    rw [show 22-level = (21-level)+1 by omega, Nat.pow_succ, Nat.mul_comm]
  have lo : 2^(22-level) ≤ Opening.lowerNode index (level+2) := by
    rw [QuartetCheck.lower_node_shift, Nat.le_div_iff_mul_le positive, low]
    omega
  have hi : Opening.lowerNode index (level+2) < 2^(23-level) := by
    rw [QuartetCheck.lower_node_shift, Nat.div_lt_iff_lt_mul positive, high]
    omega
  generalize Opening.lowerNode index (level+2) = node at lo hi ⊢
  rcases Nat.even_or_odd node with parity | parity
  · rw [Nat.xor_one_of_even parity]
    obtain ⟨k, hk⟩ := parity
    omega
  · rw [Nat.xor_one_of_odd parity]
    obtain ⟨k, hk⟩ := parity
    omega

end TwoPermutationPrototype.Packed.Checker
