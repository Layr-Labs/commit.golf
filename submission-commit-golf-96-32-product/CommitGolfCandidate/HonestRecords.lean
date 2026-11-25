import CommitGolfCandidate.CommitSemantics
import CommitGolfCandidate.OpeningOutput

/-! Authentication of the actual bytes emitted by honest opening. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Read `count` sibling digests from an actual opening output buffer. Directions
are the same leaf-index bits used by the checker image. -/
def openingProofPath (state : MachineState) (proofAddress index count : Nat) : List (Bool × Digest) :=
  (List.range count).map fun level =>
    (index.testBit level, readBuffer state (proofAddress+32+32*level) 32)

theorem opening_proof_path_length (state : MachineState) (proofAddress index count : Nat) :
    (openingProofPath state proofAddress index count).length = count := by
  simp only [openingProofPath, List.length_map, List.length_range]

/-- For non-batch openings, the 24-level path parsed from emitted proof bytes is the heap path. -/
theorem opening_proof_path (committed : MachineState) (positions : Positions)
    (notBatch : positions.card ≠ BATCH) (ordinal : Nat)
    (present : ordinal < positions.card) :
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    openingProofPath (openingResult trapdoor positions).state
      (submission.layout.proof+800*ordinal) (openingIndex positions ordinal) 24 =
    heapPath (fun slot => readBuffer committed (4294971424+heapOffset slot) 32)
      (LENGTH+openingIndex positions ordinal) 24 := by
  dsimp only
  apply List.ext_getElem
  · rw [opening_proof_path_length, heap_path_length]
  · intro level leftBound rightBound
    have inside : level < 24 := by rw [opening_proof_path_length] at leftBound; exact leftBound
    rw [heap_path_get _ _ _ _ inside]
    simp only [openingProofPath, List.getElem_map, List.getElem_range]
    apply Prod.ext
    · exact (heap_leaf_direction 24 (openingIndex positions ordinal) level
        (opening_index_bound positions ordinal) inside).symm
    · exact (opening_output_records committed positions notBatch ordinal present).2 level inside

/-- For non-batch openings, the emitted salt and path reconstruct the returned commitment. -/
theorem opening_proof_authenticates (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (positions : Positions) (notBatch : positions.card ≠ BATCH)
    (ordinal : Nat) (present : ordinal < positions.card) :
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    let opened := (openingResult trapdoor positions).state
    let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
    climb oracle.compression
      (leafDigest oracle.compression
        (readBuffer opened (submission.layout.proof+800*ordinal) 32) (message index))
      (openingProofPath opened (submission.layout.proof+800*ordinal) index.val 24) =
        readBuffer committed submission.layout.commitment 32 := by
  dsimp only
  rw [opening_proof_path committed positions notBatch ordinal present,
    (opening_output_records committed positions notBatch ordinal present).1]
  let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
  have leaf := correct.2.2 index
  change readBuffer committed (4294971424+heapOffset (LENGTH+index.val)) 32 =
    leafDigest oracle.compression (readBuffer committed (5905584160+32*index.val) 32)
      (message index) at leaf
  rw [← leaf]
  have root := reconstruct_heap_root oracle.compression
    (fun slot => readBuffer committed (4294971424+heapOffset slot) 32) 24 index.val index.isLt correct.2.1
  exact root.trans correct.1.symm

end CommitGolfCandidate
