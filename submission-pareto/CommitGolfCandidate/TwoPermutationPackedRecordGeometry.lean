import CommitGolfCandidate.TwoPermutationPackedHonestLower

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Checker (checker_positions_bound checkSourceWord)

/-- Byte cursor before consuming the sibling at this level, or after the record at level sixteen. -/
def lowerProofByte (ordinal level : Nat) : Nat :=
  checkProofByte ordinal+MixedWidth.siblingOffset level

def lowerSiblingWidth (level : Nat) : Nat := MixedWidth.siblingWidth level

theorem lower_proof_byte_next (ordinal level : Nat) :
    lowerProofByte ordinal (level+1)=lowerProofByte ordinal level+lowerSiblingWidth level := by
  simp only [lowerProofByte,lowerSiblingWidth,MixedWidth.sibling_offset_next,Nat.add_assoc]

theorem lower_proof_byte_end (ordinal : Nat) :
    lowerProofByte ordinal 16=checkProofByte (ordinal+1) := by
  unfold lowerProofByte checkProofByte MixedWidth.siblingOffset
  norm_num <;> omega

theorem packed_record_geometry (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (fits : ProofWithin input) :
    checkProofByte ordinal % 2 = 0 ∧
      checkProofByte ordinal + 500 ≤ 10334769248 + input.proof.length ∧
      32768 ≤ checkProofByte ordinal ∧
      checkProofByte ordinal + 500 ≤ MEMORY_BYTES ∧
      checkSourceWord ordinal+32 ≤ 2^33 := by
  have count := checker_positions_bound input
  obtain ⟨atLeast, atMost⟩ := fits
  unfold checkProofByte checkSourceWord MEMORY_BYTES
  omega

theorem lower_proof_geometry (ordinal level : Nat) (inside : level<16)
    (room : checkProofByte ordinal+500≤MEMORY_BYTES) :
    32768≤lowerProofByte ordinal level ∧ lowerProofByte ordinal level%2=0 ∧
      lowerProofByte ordinal level+lowerSiblingWidth level≤MEMORY_BYTES := by
  have even := MixedWidth.sibling_offset_even level
  have fits : MixedWidth.siblingOffset level+MixedWidth.siblingWidth level≤500 := by
    unfold MixedWidth.siblingOffset MixedWidth.siblingWidth
    split_ifs <;> omega
  unfold lowerProofByte lowerSiblingWidth
  unfold checkProofByte at room ⊢
  omega

theorem lower_width_from_counter (level : Nat) :
    lowerSiblingWidth level=if 15≤16-level then 32 else 30 := by
  by_cases full : level≤1
  · have counter : 15≤16-level := by omega
    simp only [lowerSiblingWidth,MixedWidth.siblingWidth,if_pos full,if_pos counter]
  · have counter : ¬15≤16-level := by omega
    simp only [lowerSiblingWidth,MixedWidth.siblingWidth,if_neg full,if_neg counter]

theorem lower_wire_sibling_from_cursor (state : MachineState) (ordinal level : Nat) :
    lowerWireSibling state ordinal level =
      if 15≤16-level then readBuffer state (lowerProofByte ordinal level) 32
      else 0#16 ++ readBuffer state (lowerProofByte ordinal level) 30 := by
  by_cases full : level≤1
  · have counter : 15≤16-level := by omega
    simp only [lowerWireSibling,lowerProofByte,if_pos full,if_pos counter]
  · have counter : ¬15≤16-level := by omega
    simp only [lowerWireSibling,lowerProofByte,if_neg full,if_neg counter]

theorem lower_wire_sibling_frame (before after : MachineState) (ordinal level : Nat)
    (frame : ∀ j<lowerSiblingWidth level,
      memoryView after ((lowerProofByte ordinal level+j)/8)=
        memoryView before ((lowerProofByte ordinal level+j)/8)) :
    lowerWireSibling after ordinal level=lowerWireSibling before ordinal level := by
  by_cases full : level≤1
  · have words : ∀ j<32,
        memoryView after ((checkProofByte ordinal+MixedWidth.siblingOffset level+j)/8)=
          memoryView before ((checkProofByte ordinal+MixedWidth.siblingOffset level+j)/8) := by
      simpa only [lowerSiblingWidth,MixedWidth.siblingWidth,lowerProofByte,if_pos full] using frame
    simpa only [lowerWireSibling,if_pos full] using buffer_byte_frame before after _ 32 words
  · have words : ∀ j<30,
        memoryView after ((checkProofByte ordinal+MixedWidth.siblingOffset level+j)/8)=
          memoryView before ((checkProofByte ordinal+MixedWidth.siblingOffset level+j)/8) := by
      simpa only [lowerSiblingWidth,MixedWidth.siblingWidth,lowerProofByte,if_neg full] using frame
    simp only [lowerWireSibling,if_neg full,buffer_byte_frame before after _ 30 words]

end TwoPermutationPrototype.Packed.Checker
