import CommitGolfCandidate.QOpeningProofBytes
import CommitGolfCandidate.QuadOpeningLevel
import CommitGolfCandidate.PentaCapSpec

/-! The cap proof bytes as a function of the trapdoor (912-byte records, then the table of levels
7-10), and their agreement with the cap transcript builder whenever the trapdoor slots hold the
penta tree nodes and the salts. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling OracleComp
open QOpening (trapdoorSalt)

/-- One 912-byte record read from the trapdoor: the salt and the siblings of levels 0-6. -/
def trapdoorRecord {s : Submission} (trapdoor : BitVec (8*s.sizes.trapdoor)) (index : Index) : List Byte :=
  saltBytes (trapdoorSalt (s := s) trapdoor index) ++
  (List.range 7).flatMap fun k =>
    (List.range 4).flatMap fun j => digestBytes (pentaTrapdoorNode trapdoor k (pentaNeighbour index k j))

/-- The 8,800-byte table read from the trapdoor: every slot of levels 7-10. -/
def trapdoorTable {n : Nat} (trapdoor : BitVec n) : List Byte :=
  [7, 8, 9, 10].flatMap fun k =>
    (List.range (capSlots k)).flatMap fun j => digestBytes (pentaTrapdoorNode trapdoor k j)

def proofFromTrapdoor {s : Submission} (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) : Proof :=
  (positions.sort (· ≤ ·)).flatMap (trapdoorRecord (s := s) trapdoor) ++
    (if positions.card = 0 then [] else (trapdoorTable trapdoor).take 8704)

private theorem sorted_value_indices (positions : Positions) :
    (positions.attach.sort (fun i j => i.val ≤ j.val)).map Subtype.val =
      positions.sort (· ≤ ·) := by
  have mapped := Finset.map_sort (r := fun i j : {i // i ∈ positions} => i.val ≤ j.val)
    (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ positions))
    (s := positions.attach) (by intro a _ b _; rfl)
  simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using mapped

theorem neighbour_inside (index : Index) (k j : Nat) :
    pentaNeighbour index k j < 5 * pentaCount (k+1) := by
  have count := div_lt_count index.val index.isLt (k+1)
  have slot := (pentaRot index k j).isLt
  unfold pentaNeighbour
  omega

/-- The pure transcript reconstructed from the trapdoor slots agrees with the cap transcript
builder when the slots of levels 0-10 hold the penta nodes and the opened salts agree. -/
theorem proof_from_trapdoor_matches_opened (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (penta : PentaFunction) (leaves : DigestTape) (salts : CompleteSaltTape)
    (node : ∀ level j, level < PENTA_LEVELS → j < 5 * pentaCount (level + 1) →
      pentaTrapdoorNode trapdoor level j = pentaNode penta leaves level j)
    (salt : ∀ index ∈ positions, trapdoorSalt (s := s) trapdoor index = salts index) :
    proofFromTrapdoor (s := s) trapdoor positions =
      (capTranscriptBuilder penta positions (fun i => salts i.val) leaves).2 := by
  unfold proofFromTrapdoor capTranscriptBuilder
  dsimp only
  rw [← sorted_value_indices positions, List.flatMap_map]
  congr 1
  · apply List.flatMap_congr
    intro index _
    unfold trapdoorRecord capRecord
    rw [salt index.val index.property]
    congr 1
    apply List.flatMap_congr
    intro k member
    apply List.flatMap_congr
    intro j _
    have small : k < PENTA_LEVELS := by
      have := List.mem_range.mp member
      unfold PENTA_LEVELS
      omega
    rw [node k _ small (neighbour_inside index.val k j)]
  · split
    · rfl
    · apply congrArg (List.take 8704)
      unfold trapdoorTable capTable capLevel
      apply List.flatMap_congr
      intro k member
      apply List.flatMap_congr
      intro j hj
      have small : k < PENTA_LEVELS := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        unfold PENTA_LEVELS
        omega
      rw [node k j small (by have := List.mem_range.mp hj; unfold capSlots at this; exact this)]

end TwoPermutationPrototype.QuadOpening
