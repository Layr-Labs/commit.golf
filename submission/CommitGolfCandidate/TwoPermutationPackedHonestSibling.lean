import CommitGolfCandidate.TwoPermutationPackedHonestLower
import CommitGolfCandidate.K3T238PackDecode

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (RecordInputFrame honestIndex)
open TwoPermutationPrototype.QuartetCertificate (honestCheckInput)
open TwoPermutationPrototype.PackedHonest (honestHeap honest_projected_node honest_projected238_node)
set_option maxRecDepth 8192

/-- The proof's upper sibling at loop level `level` is the honest heap node beside
`lowerNode (flipIndex index) (level+2)`, the checker's path. -/
theorem canonical_lower_wire_sibling (oracle : Oracle) (message : Message)
    (positions : Positions) (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card)
    (state : MachineState) (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state)
    (level : Nat) (within : level < 14) :
    lowerWireSibling state ordinal level =
      honestHeap oracle message salts (Opening.lowerNode (QuartetCheck.flipIndex (honestIndex positions ordinal present).val) (level+2) ^^^ 1) := by
  have range := lower_sibling_range (QuartetCheck.flipIndex (honestIndex positions ordinal present).val) level within
  unfold lowerWireSibling
  by_cases small : level ≤ 1
  · rw [if_pos small]
    have byte : lowerProofByte ordinal level = checkProofByte ordinal+112+32*level := by
      unfold lowerProofByte
      rw [if_pos small]
    rw [byte]
    rcases (show level = 0 ∨ level = 1 by omega) with zero | one
    · subst zero
      rw [show checkProofByte ordinal+112+32*0 = checkProofByte ordinal+112 by omega]
      exact packed_record_first_sibling oracle message positions salts ordinal present state framed
    · subst one
      rw [show checkProofByte ordinal+112+32*1 = checkProofByte ordinal+144 by omega]
      exact packed_record_second_sibling oracle message positions salts ordinal present state framed
  · rw [if_neg small]
    by_cases mid : level ≤ 5
    · rw [if_pos mid]
      have byte : lowerProofByte ordinal level = checkProofByte ordinal+176+30*(level-2) := by
        unfold lowerProofByte
        rw [if_neg small, if_pos (show level ≤ 13 by omega)]
      rw [byte, packed_record_mid_sibling oracle message positions salts ordinal present state framed (level-2)
        (by omega), show level-2+4 = level+2 by omega]
      have top : 2^(23-level) ≤ 2^21 := Nat.pow_le_pow_right (by decide) (by omega)
      have bottom : 1 ≤ 2^(22-level) := Nat.one_le_two_pow
      exact honest_projected_node _ _ _ _ (by omega) (by omega)
    · rw [if_neg mid]
      let nodes := (List.range 8).map (fun k =>
        honestHeap oracle message salts (Opening.lowerNode (QuartetCheck.flipIndex (honestIndex positions ordinal present).val) (k+8) ^^^ 1))
      have six : lowerProofByte ordinal 6 = checkProofByte ordinal+296 := by
        unfold lowerProofByte
        rw [if_neg (show ¬ (6 ≤ 1) by decide), if_pos (show 6 ≤ 13 by decide)]
      rw [packed_sibling_of_bytes state ordinal nodes (by simp [nodes]) (by
          intro j inside
          rw [six]
          exact packed_record_block_byte oracle message positions salts ordinal present state framed j inside)
        level (by omega) within]
      have entry : nodes[level-6]! =
          honestHeap oracle message salts (Opening.lowerNode (QuartetCheck.flipIndex (honestIndex positions ordinal present).val) (level+2) ^^^ 1) := by
        rw [getElem!_pos nodes (level-6) (by simp [nodes]; omega)]
        simp only [nodes, List.getElem_map, List.getElem_range]
        rw [show level-6+8 = level+2 by omega]
      rw [entry]
      have top : 2^(23-level) ≤ 2^17 := Nat.pow_le_pow_right (by decide) (by omega)
      have bottom : 1 ≤ 2^(22-level) := Nat.one_le_two_pow
      exact honest_projected238_node _ _ _ _ (by omega) (by omega)

end TwoPermutationPrototype.Packed.Checker
