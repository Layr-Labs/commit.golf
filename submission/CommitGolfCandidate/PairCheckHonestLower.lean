-- Pair-heads copy of TwoPermutationPackedHonestLower (stack/check/work/mkcopy.py); edits below are marked PAIR.
import CommitGolfCandidate.PairCheckCheckRecordData
import CommitGolfCandidate.PairCheckModel
import CommitGolfCandidate.PairCheckNamespaces

namespace TwoPermutationPrototype.PairCk.Packed.Checker
open  TwoPermutationPrototype.Packed TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.PairCk.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (RecordInputFrame honestIndex)
open TwoPermutationPrototype.PairCertificate (pairHonestCheckInput)
open TwoPermutationPrototype.PairCk.PackedHonest (honestHeap honest_projected_node)
set_option maxRecDepth 8192

def lowerWireSibling (state : MachineState) (ordinal level : Nat) : Digest :=
  if level = 0 then readBuffer state (checkProofByte ordinal+112) 32
  else 0#16 ++ readBuffer state (checkProofByte ordinal+144+30*(level-1)) 30

/-- The proof's upper sibling at Quartet level `level` is the honest heap node beside
`lowerNode index (level+2)`. -/
theorem canonical_lower_wire_sibling (oracle : Oracle) (message : Message)
    (positions : Positions) (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card)
    (state : MachineState) (framed : RecordInputFrame (pairHonestCheckInput oracle message positions salts) ordinal state)
    (level : Nat) (within : level < 14) :
    lowerWireSibling state ordinal level =
      honestHeap oracle message salts (Opening.lowerNode (honestIndex positions ordinal present) (level+2) ^^^ 1) := by
  by_cases first : level = 0
  · subst level
    simpa only [lowerWireSibling, ite_true] using
      packed_record_first_sibling oracle message positions salts ordinal present state framed
  · rw [lowerWireSibling, ite_eq_right first]
    let slot := level-1
    have restored : slot+3=level+2 := by unfold slot; omega
    have actual := packed_record_later_sibling oracle message positions salts ordinal present state framed slot (by
      unfold slot
      omega)
    rw [restored] at actual
    rw [actual]
    obtain ⟨lo,hi⟩ := QuartetCheck.lower_node_sibling_internal (honestIndex positions ordinal present) level (by omega) within
    exact honest_projected_node _ _ _ _ lo hi

end TwoPermutationPrototype.PairCk.Packed.Checker
