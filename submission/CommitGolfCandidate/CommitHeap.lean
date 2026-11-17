import CommitGolfCandidate.S3LeavesMemory
import CommitGolfCandidate.S3TreeExec
import CommitGolfCandidate.ParentRefinement

/-! The heap built by the stage-3 commitment: the appended leaf phase leaves the stage-3
digest of every input entry in its leaf slot (S3LeavesMemory), and the retained parent loop
makes every internal node the compression of its children. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem parents_start_heap (state : MachineState) :
    (commitParentsStartState state).getReg .x9 = state.getReg .x9 :=
  commit_parents_start_register state .x9 (by simp)

private theorem parents_start_memory (state : MachineState) :
    (commitParentsStartState state).mem = state.mem := commit_parents_start_memory state

private theorem ready_heap (message : Message) {bits : Nat} (answer : BitVec bits) :
    (s3CommitReady message answer).getReg .x9 = BitVec.ofNat 64 4294971424 :=
  (s3_ready_register message answer .x9 (by decide)).trans (commit_input_registers message answer).2.1

private theorem ready_total (message : Message) {bits : Nat} (answer : BitVec bits) :
    (s3CommitReady message answer).getReg .x19 = BitVec.ofNat 64 LENGTH :=
  (s3_ready_register message answer .x19 (by decide)).trans
    (commit_input_registers message answer).2.2.2.1

attribute [local irreducible] s3Leaves commitParents s3CommitReady checkEvaluation

/-- The leaf phase and the parent loop together construct a consistent heap whose leaves are
the stage-3 digests of the input entries. No hypothesis about heap contents is required. -/
theorem commit_input_tree (oracle : Oracle) (message : Message)
    (answer : BitVec (192*LENGTH)) :
    let leaves := (checkEvaluation oracle (s3Leaves (s3CommitReady message answer) (2^18))).1
    let finished := (checkEvaluation oracle (commitParents (commitParentsStartState leaves) (LENGTH-1))).1
    HeapParents oracle.compression finished 4294971424 LENGTH 0 ∧
      ∀ index : Index, heapDigest finished 4294971424 (LENGTH+index.val) =
        s3LeafDigest oracle.permutation (expandNonce192 (answer.extractLsb' (192*index.val) 192))
          (message index) := by
  let ready := s3CommitReady message answer
  let leaves := (checkEvaluation oracle (s3Leaves ready (2^18))).1
  let parents := commitParentsStartState leaves
  have leafRegs (reg : Reg) (member : reg ∈ [Reg.x9, .x19, .x26]) :
      leaves.getReg reg = ready.getReg reg := s3_leaves_register oracle ready (2^18) reg member
  have parentHeap : parents.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (parents_start_heap leaves).trans ((leafRegs .x9 (by simp)).trans (ready_heap message answer))
  have parentCounter : ParentPointerInvariant parents (LENGTH-1) := by
    apply commit_parents_start_pointers_of_count leaves LENGTH
    · exact (leafRegs .x19 (by simp)).trans (ready_total message answer)
    · decide
    · decide
  constructor
  · exact commit_parents_heap oracle parents 4294971424 LENGTH (by decide)
      parentHeap parentCounter (by decide) (by decide)
  · intro index
    have indexBound : index.val < 2^24 := index.isLt
    change heapDigest (checkEvaluation oracle (commitParents parents (LENGTH-1))).1
      4294971424 (LENGTH+index.val) = _
    rw [commit_parents_preserves_digest oracle parents 4294971424 (LENGTH-1)
      (LENGTH+index.val) parentHeap parentCounter
      (by change 16777216-1 < 16777216+index.val; omega)
      (by change 4294971424+32*(16777216+index.val)+32 ≤ 2^64; omega)]
    have address : 4294971424+32*(LENGTH+index.val) = 4831842336+32*index.val := by
      change 4294971424+32*(16777216+index.val) = _
      omega
    unfold heapDigest
    rw [read_buffer_memory_congr _ _ (parents_start_memory leaves), address]
    exact s3_leaves_digest oracle message answer index

/-- Every path through that constructed heap reconstructs the root from the
corresponding stage-3 leaf digest. -/
theorem commit_input_tree_reconstruct (oracle : Oracle) (message : Message)
    (answer : BitVec (192*LENGTH)) (index : Index) :
    let leaves := (checkEvaluation oracle (s3Leaves (s3CommitReady message answer) (2^18))).1
    let finished := (checkEvaluation oracle (commitParents (commitParentsStartState leaves) (LENGTH-1))).1
    climb oracle.compression
      (s3LeafDigest oracle.permutation (expandNonce192 (answer.extractLsb' (192*index.val) 192))
        (message index))
      (heapPath (heapDigest finished 4294971424) (LENGTH+index.val) LOG_LENGTH) =
        heapDigest finished 4294971424 1 := by
  have tree := commit_input_tree oracle message answer
  dsimp only
  rw [← tree.2 index]
  exact reconstruct_heap_root oracle.compression _ LOG_LENGTH index.val index.isLt tree.1

end CommitGolfCandidate
