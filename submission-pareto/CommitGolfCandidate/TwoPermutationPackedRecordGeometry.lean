import CommitGolfCandidate.TwoPermutationPackedHonestLower

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Checker (checker_positions_bound checkSourceWord)

theorem packed_record_geometry (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (fits : ProofWithin input) :
    checkProofByte ordinal % 2 = 0 ∧
      checkProofByte ordinal + 534 ≤ 13824430176 + input.proof.length ∧
      32768 ≤ checkProofByte ordinal ∧
      checkProofByte ordinal + 534 ≤ MEMORY_BYTES ∧
      checkSourceWord ordinal+32 ≤ 2^33 := by
  have count := checker_positions_bound input
  obtain ⟨atLeast, atMost⟩ := fits
  unfold checkProofByte checkSourceWord MEMORY_BYTES
  omega

/-- The loop reads two bytes past the last record's sibling block (the 30-byte copy at loop level 13). -/
theorem packed_record_room (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (fits : ProofWithin input) :
    checkProofByte ordinal + 536 ≤ MEMORY_BYTES := by
  have count := checker_positions_bound input
  obtain ⟨atLeast, atMost⟩ := fits
  unfold checkProofByte MEMORY_BYTES
  omega

theorem lower_proof_geometry (ordinal level : Nat) (inside : level<14)
    (room : checkProofByte ordinal+536 ≤ MEMORY_BYTES) :
    32768 ≤ lowerProofByte ordinal level ∧ lowerProofByte ordinal level % 2 = 0 ∧
      lowerProofByte ordinal level+lowerSiblingWidth level ≤ MEMORY_BYTES :=
  lower_proof_byte_bounds ordinal level inside room

/-- Loop levels `L ≤ 4` (L21's part of the loop): 32-byte siblings at `L ≤ 1`, 30-byte siblings at `L = 2..4`. -/
theorem lower_sibling_width_low (level : Nat) (low : level ≤ 4) :
    lowerSiblingWidth level = if level ≤ 1 then 32 else 30 := by
  unfold lowerSiblingWidth
  split
  · rfl
  · rw [if_pos (by omega)]

theorem lower_wire_sibling_low (state : MachineState) (ordinal level : Nat) (low : level ≤ 4) :
    lowerWireSibling state ordinal level =
      if level ≤ 1 then readBuffer state (lowerProofByte ordinal level) 32
      else 0#16 ++ readBuffer state (lowerProofByte ordinal level) 30 := by
  unfold lowerWireSibling
  split
  · rfl
  · rw [if_pos (by omega)]

/-- The siblings of a record depend only on its bytes `112..534`. -/
theorem lower_wire_sibling_frame (before after : MachineState) (ordinal level : Nat) (inside : level < 14)
    (frame : ∀ j < 422, memoryView after ((checkProofByte ordinal+112+j)/8) =
      memoryView before ((checkProofByte ordinal+112+j)/8)) :
    lowerWireSibling after ordinal level=lowerWireSibling before ordinal level := by
  unfold lowerWireSibling
  by_cases low : level ≤ 1
  · have words : ∀ j < 32, memoryView after ((lowerProofByte ordinal level+j)/8) =
        memoryView before ((lowerProofByte ordinal level+j)/8) := by
      intro j hj
      have := frame (32*level+j) (by omega)
      simp only [lowerProofByte, low, ite_true]
      rwa [show checkProofByte ordinal+112+32*level+j = checkProofByte ordinal+112+(32*level+j) by omega]
    rw [if_pos low, if_pos low, buffer_byte_frame before after _ 32 words]
  · by_cases mid : level ≤ 5
    · have words : ∀ j < 30, memoryView after ((lowerProofByte ordinal level+j)/8) =
          memoryView before ((lowerProofByte ordinal level+j)/8) := by
        intro j hj
        have := frame (64+30*(level-2)+j) (by omega)
        simp only [lowerProofByte, low, ite_false, show level ≤ 13 by omega, ite_true]
        rwa [show checkProofByte ordinal+176+30*(level-2)+j = checkProofByte ordinal+112+(64+30*(level-2)+j) by omega]
      rw [if_neg low, if_neg low, if_pos mid, if_pos mid, buffer_byte_frame before after _ 30 words]
    · rw [if_neg low, if_neg low, if_neg mid, if_neg mid]
      apply packed_sibling_frame before after ordinal level (by omega) inside
      intro j hj
      have := frame (184+j) (by omega)
      simp only [lowerProofByte, show ¬ (6 ≤ 1) by decide, ite_false, show 6 ≤ 13 by decide, ite_true]
      rwa [show checkProofByte ordinal+176+30*(6-2)+j = checkProofByte ordinal+112+(184+j) by omega]

end TwoPermutationPrototype.Packed.Checker
