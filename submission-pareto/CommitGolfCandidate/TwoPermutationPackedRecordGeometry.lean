import CommitGolfCandidate.TwoPermutationPackedHonestLower

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Checker (checker_positions_bound checkSourceWord)

/-- Byte cursor before consuming the sibling at this level, or after the record at level sixteen. -/
def lowerProofByte (ordinal level : Nat) : Nat := checkProofByte ordinal+16+30*level

def lowerSiblingWidth (_level : Nat) : Nat := 30

theorem lower_proof_byte_next (ordinal level : Nat) :
    lowerProofByte ordinal (level+1) = lowerProofByte ordinal level+lowerSiblingWidth level := by
  unfold lowerProofByte lowerSiblingWidth
  omega

theorem lower_proof_byte_end (ordinal : Nat) :
    lowerProofByte ordinal 16 = checkProofByte (ordinal+1) := by
  unfold lowerProofByte checkProofByte
  omega

theorem packed_record_geometry (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (fits : ProofWithin input) :
    checkProofByte ordinal % 2 = 0 ∧
      checkProofByte ordinal + 496 ≤ 10334769248 + input.proof.length ∧
      32768 ≤ checkProofByte ordinal ∧
      checkProofByte ordinal + 496 ≤ MEMORY_BYTES ∧
      checkSourceWord ordinal+32 ≤ 2^33 := by
  have count := checker_positions_bound input
  obtain ⟨atLeast, atMost⟩ := fits
  unfold checkProofByte checkSourceWord MEMORY_BYTES
  omega

theorem lower_proof_geometry (ordinal level : Nat) (inside : level<16)
    (room : checkProofByte ordinal+496 ≤ MEMORY_BYTES) :
    32768 ≤ lowerProofByte ordinal level ∧ lowerProofByte ordinal level % 2 = 0 ∧
      lowerProofByte ordinal level+lowerSiblingWidth level ≤ MEMORY_BYTES := by
  unfold lowerProofByte lowerSiblingWidth
  unfold checkProofByte at room ⊢
  omega

theorem lower_wire_sibling_frame (before after : MachineState) (ordinal level : Nat)
    (frame : ∀ j < lowerSiblingWidth level,
      memoryView after ((lowerProofByte ordinal level+j)/8) =
        memoryView before ((lowerProofByte ordinal level+j)/8)) :
    lowerWireSibling after ordinal level=lowerWireSibling before ordinal level := by
  have words : ∀ j < 30, memoryView after ((checkProofByte ordinal+16+30*level+j)/8) =
      memoryView before ((checkProofByte ordinal+16+30*level+j)/8) := by
    simpa only [lowerSiblingWidth,lowerProofByte] using frame
  unfold lowerWireSibling
  rw [buffer_byte_frame before after _ 30 words]

end TwoPermutationPrototype.Packed.Checker
