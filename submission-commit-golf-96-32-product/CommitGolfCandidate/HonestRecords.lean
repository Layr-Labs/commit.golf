import CommitGolfCandidate.CommitSemantics
import CommitGolfCandidate.OpeningOutput

/-! Authentication of the actual bytes emitted by honest opening. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Read the 24 sibling digests from an actual opening output buffer. Directions
are the same leaf-index bits used by the checker image. -/
def openingProofPath (state : MachineState) (proofAddress index : Nat) : List (Bool × Digest) :=
  (List.range 24).map fun level =>
    (index.testBit level, readBuffer state (proofAddress+32+32*level) 32)

theorem opening_proof_path_length (state : MachineState) (proofAddress index : Nat) :
    (openingProofPath state proofAddress index).length = 24 := by
  simp only [openingProofPath, List.length_map, List.length_range]

/-- The path parsed from emitted proof bytes is exactly the private heap's path. -/
theorem opening_proof_path (committed : MachineState) (positions : Positions) (ordinal : Nat)
    (present : ordinal < positions.card) :
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    openingProofPath (openingResult trapdoor positions).state
      (submission.layout.proof+800*ordinal) (openingIndex positions ordinal) =
    heapPath (fun slot => readBuffer committed (4294971424+32*slot) 32)
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
    · exact (opening_output_records committed positions ordinal present).2 level inside

/-- The salt and path actually emitted by opening reconstruct the returned
commitment for every selected leaf, provided the actual commitment state has the
proved tree invariant. No assumption is made about compression being collision-free. -/
theorem opening_proof_authenticates (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (positions : Positions) (ordinal : Nat) (present : ordinal < positions.card) :
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    let opened := (openingResult trapdoor positions).state
    let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
    climb oracle.compression
      (leafDigest oracle.compression
        (readBuffer opened (submission.layout.proof+800*ordinal) 32) (message index))
      (openingProofPath opened (submission.layout.proof+800*ordinal) index.val) =
        readBuffer committed submission.layout.commitment 32 := by
  dsimp only
  rw [opening_proof_path committed positions ordinal present,
    (opening_output_records committed positions ordinal present).1]
  let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
  have leaf := correct.2.2 index
  change readBuffer committed (4294971424+32*(LENGTH+index.val)) 32 =
    leafDigest oracle.compression (readBuffer committed (5368713248+32*index.val) 32)
      (message index) at leaf
  rw [← leaf]
  have root := reconstruct_heap_root oracle.compression
    (fun slot => readBuffer committed (4294971424+32*slot) 32) 24 index.val index.isLt correct.2.1
  exact root.trans correct.1.symm

/-- The same authentication statement for every supported result of the submitted
commitment program. The tree invariant is proved from execution, not assumed here. -/
theorem honest_machine_proof_authenticates (oracle : Oracle) (message : Message)
    (committed : Execution × Nat)
    (reachable : committed ∈ support (oracle.run (submission.run .commit message)))
    (positions : Positions) (ordinal : Nat) (present : ordinal < positions.card) :
    let trapdoor := readBuffer committed.1.state submission.layout.trapdoor submission.sizes.trapdoor
    let opened := (openingResult trapdoor positions).state
    let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
    climb oracle.compression
      (leafDigest oracle.compression
        (readBuffer opened (submission.layout.proof+800*ordinal) 32) (message index))
      (openingProofPath opened (submission.layout.proof+800*ordinal) index.val) =
        readBuffer committed.1.state submission.layout.commitment 32 :=
  opening_proof_authenticates oracle message committed.1.state
    (commit_run_matches oracle message committed reachable) positions ordinal present

end CommitGolfCandidate
