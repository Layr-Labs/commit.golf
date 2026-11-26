import CommitGolfCandidate.CommitSemantics
import CommitGolfCandidate.OpeningOutput

/-! Authentication of the actual bytes emitted by honest opening: the 128 cap
digests, and for every opened leaf its salt and the 17 siblings up to its cap node. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Read the 17 sibling digests of one opening record. Directions are the same
leaf-index bits used by the checker image. -/
def openingProofPath (state : MachineState) (proofAddress index : Nat) : List (Bool × Digest) :=
  (List.range PATH_LEVELS).map fun level =>
    (index.testBit level, readBuffer state (proofAddress+24+32*level) 32)

theorem opening_proof_path_length (state : MachineState) (proofAddress index : Nat) :
    (openingProofPath state proofAddress index).length = PATH_LEVELS := by
  simp only [openingProofPath, List.length_map, List.length_range]

/-- The path parsed from an emitted record is exactly the private heap's path from
the leaf up to (but excluding) its cap node. -/
theorem opening_proof_path (committed : MachineState) (positions : Positions) (ordinal : Nat)
    (present : ordinal < positions.card) :
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    openingProofPath (openingResult trapdoor positions).state
      (submission.layout.proof+4096+568*ordinal) (openingIndex positions ordinal) =
    heapPath (fun slot => readBuffer committed (4294971424+heapOffset slot) 32)
      (LENGTH+openingIndex positions ordinal) PATH_LEVELS := by
  dsimp only
  apply List.ext_getElem
  · rw [opening_proof_path_length, heap_path_length]
  · intro level leftBound rightBound
    have inside : level < PATH_LEVELS := by rw [opening_proof_path_length] at leftBound; exact leftBound
    rw [heap_path_get _ _ _ _ inside]
    simp only [openingProofPath, List.getElem_map, List.getElem_range]
    apply Prod.ext
    · exact (heap_leaf_direction 24 (openingIndex positions ordinal) level
        (opening_index_bound positions ordinal) (by change level < 17 at inside; omega)).symm
    · exact ((opening_output_records committed positions).2 ordinal present).2 level inside

/-- The cap node above leaf `index`. -/
theorem leaf_cap_node (index : Nat) :
    (LENGTH+index)/2^PATH_LEVELS = 128 + index/2^PATH_LEVELS := by
  rw [show LENGTH + index = index + 128 * 2^PATH_LEVELS from by
    change 16777216 + index = index + 128 * 2^17; omega]
  rw [Nat.add_mul_div_right _ _ (by positivity)]
  omega

/-- The salt and path emitted by opening reconstruct the leaf's cap node in the
committed heap, provided the commitment state has the proved tree invariant. No
assumption is made about compression being collision-free. -/
theorem opening_proof_authenticates (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (positions : Positions) (ordinal : Nat) (present : ordinal < positions.card) :
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    let opened := (openingResult trapdoor positions).state
    let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
    climb oracle.compression
      (leafDigest oracle.compression
        (saltState (readBuffer opened (submission.layout.proof+4096+568*ordinal) 24)) (message index))
      (openingProofPath opened (submission.layout.proof+4096+568*ordinal) index.val) =
        heapDigest committed 4294971424 (128 + index.val/2^PATH_LEVELS) := by
  dsimp only
  rw [opening_proof_path committed positions ordinal present,
    ((opening_output_records committed positions).2 ordinal present).1]
  let index : Index := ⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩
  have leaf := correct.2.2 index
  change readBuffer committed (4294971424+heapOffset (LENGTH+index.val)) 32 =
    leafDigest oracle.compression (saltState (readBuffer committed (5905584160+24*index.val) 24))
      (message index) at leaf
  rw [← leaf]
  have indexBound : index.val < LENGTH := index.isLt
  have reached := reconstruct_heap_ancestor_above oracle.compression
    (fun slot => readBuffer committed (4294971424+heapOffset slot) 32) 127 LENGTH correct.2.1
    PATH_LEVELS (LENGTH+index.val) (by omega)
    (by change 128 * 2^17 ≤ 16777216 + index.val; omega)
  rw [leaf_cap_node] at reached
  exact reached

/-- The 128 cap digests emitted by opening are the committed heap's cap. -/
theorem opening_proof_cap (committed : MachineState) (positions : Positions)
    (node : Nat) (inside : node < 128) :
    let trapdoor := readBuffer committed submission.layout.trapdoor submission.sizes.trapdoor
    readBuffer (openingResult trapdoor positions).state (submission.layout.proof+32*node) 32 =
      heapCap committed 4294971424 node := by
  dsimp only
  rw [(opening_output_records committed positions).1 node inside]
  simp only [heapCap, if_pos inside]
  rfl

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
        (saltState (readBuffer opened (submission.layout.proof+4096+568*ordinal) 24)) (message index))
      (openingProofPath opened (submission.layout.proof+4096+568*ordinal) index.val) =
        heapDigest committed.1.state 4294971424 (128 + index.val/2^PATH_LEVELS) :=
  opening_proof_authenticates oracle message committed.1.state
    (commit_run_matches oracle message committed reachable) positions ordinal present

end CommitGolfCandidate
