import CommitGolfCandidate.QOpeningProofBytes
import CommitGolfCandidate.QuadOpeningLevel
import CommitGolfCandidate.PentaCapSpec

/-! The hybrid proof bytes as a function of the trapdoor (720-byte records, then the 132 level-13
nodes), and their agreement with the cap transcript builder whenever the trapdoor slots hold the
tree's groups and the salts. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling OracleComp
open QOpening (trapdoorSalt)

/-- One 720-byte record read from the trapdoor. -/
def trapdoorRecord {s : Submission} (trapdoor : BitVec (8*s.sizes.trapdoor)) (index : Index) : List Byte :=
  saltBytes (trapdoorSalt (s := s) trapdoor index) ++
  ((List.range PENTA_LOW).flatMap fun k =>
    (List.range 4).flatMap fun j =>
      digestBytes (pentaTrapdoorSlot trapdoor k (index.val / placeValue (k + 1)) (pentaRot index k j).val)) ++
  ((List.range (CAP_LEVEL - PENTA_LOW)).flatMap fun m =>
    digestBytes (pentaTrapdoorSlot trapdoor (PENTA_LOW + m) (index.val / placeValue (PENTA_LOW + m + 1))
      (binSibling index (PENTA_LOW + m)).val))

/-- The 132 level-13 nodes read from the trapdoor (slot `j % 5` of 5-ary group `j / 5`). -/
def trapdoorTable {n : Nat} (trapdoor : BitVec n) : List Byte :=
  (List.range (pentaCount CAP_LEVEL)).flatMap fun j => digestBytes (pentaTrapdoorSlot trapdoor CAP_LEVEL (j/5) (j%5))

def proofFromTrapdoor {s : Submission} (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) : Proof :=
  (positions.sort (· ≤ ·)).flatMap (trapdoorRecord (s := s) trapdoor) ++
    (if positions.card = 0 then [] else trapdoorTable trapdoor)

private theorem sorted_value_indices (positions : Positions) :
    (positions.attach.sort (fun i j => i.val ≤ j.val)).map Subtype.val =
      positions.sort (· ≤ ·) := by
  have mapped := Finset.map_sort (r := fun i j : {i // i ∈ positions} => i.val ≤ j.val)
    (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ positions))
    (s := positions.attach) (by intro a _ b _; rfl)
  simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using mapped

set_option maxHeartbeats 2000000 in
/-- The pure transcript reconstructed from the trapdoor slots agrees with the cap transcript
builder when the slots of levels 0-20 hold the tree's groups and the opened salts agree. -/
theorem proof_from_trapdoor_matches_opened (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (penta : PentaFunction) (leaves : DigestTape) (salts : CompleteSaltTape)
    (slot : ∀ level g (t : Fin 5), level < PENTA_LEVELS → g < pentaCount (level + 1) →
      pentaTrapdoorSlot trapdoor level g t.val = pentaGroup penta leaves level g t)
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
    have inside := index.val.isLt
    have A : ((List.range PENTA_LOW).flatMap fun k => (List.range 4).flatMap fun j =>
        digestBytes (pentaTrapdoorSlot trapdoor k (index.val.val / placeValue (k + 1)) (pentaRot index.val k j).val)) =
      ((List.range PENTA_LOW).flatMap fun k => (List.range 4).flatMap fun j =>
        digestBytes (pentaGroup penta leaves k (index.val.val / placeValue (k + 1)) (pentaRot index.val k j))) := by
      apply List.flatMap_congr
      intro k member
      have hk : k < 3 := List.mem_range.mp member
      apply List.flatMap_congr
      intro j _
      rw [slot k _ _ (by unfold PENTA_LEVELS; omega) (div_lt_count index.val.val inside (k+1))]
    have B : ((List.range (CAP_LEVEL - PENTA_LOW)).flatMap fun m =>
        digestBytes (pentaTrapdoorSlot trapdoor (PENTA_LOW + m) (index.val.val / placeValue (PENTA_LOW + m + 1))
          (binSibling index.val (PENTA_LOW + m)).val)) =
      ((List.range (CAP_LEVEL - PENTA_LOW)).flatMap fun m =>
        digestBytes (pentaGroup penta leaves (PENTA_LOW + m) (index.val.val / placeValue (PENTA_LOW + m + 1))
          (binSibling index.val (PENTA_LOW + m)))) := by
      apply List.flatMap_congr
      intro m member
      have hm : m < 10 := List.mem_range.mp member
      rw [slot (PENTA_LOW+m) _ _ (by unfold PENTA_LEVELS PENTA_LOW; omega)
        (div_lt_count index.val.val inside (PENTA_LOW+m+1))]
    rw [A, B]
  · split
    · rfl
    · unfold trapdoorTable capLevel
      apply List.flatMap_congr
      intro j hj
      have hj' : j < 132 := by have := List.mem_range.mp hj; rwa [cap_count_value] at this
      rw [slot CAP_LEVEL (j/5) ⟨j%5, by omega⟩ (by decide) (by
        change j/5 < pentaCount 14; have : pentaCount 14 = 27 := by decide
        omega)]
      unfold pentaGroup
      rw [if_pos (by simp [slot_base_high CAP_LEVEL (by decide)])]
      congr 2
      unfold childIndex
      rw [radix_high CAP_LEVEL (by decide), slot_base_high CAP_LEVEL (by decide)]
      simp only [Fin.val_mk]
      omega

end TwoPermutationPrototype.QuadOpening
