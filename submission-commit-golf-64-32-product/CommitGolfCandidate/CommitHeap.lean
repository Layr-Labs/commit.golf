import CommitGolfCandidate.LeafHeap
import CommitGolfCandidate.ParentRefinement
import CommitGolfCandidate.BufferRefinement
import CommitGolfCandidate.CommitInput

/-! Leaf contents established from the real commitment ABI and private salt reply. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem setup_memory (state : MachineState) :
    (commitSetupState state).mem = state.mem := rfl

private theorem ready_memory (state : MachineState) :
    (commitReadyState state).mem = state.mem := rfl

private theorem initialized_memory (initial : MachineState) {bits : Nat} (answer : BitVec bits)
    (destination : Word) (pointer : initial.getReg .x12+1073741824 = destination) :
    (commitReadyState (writeBits (commitSetupState initial)
      ((commitSetupState initial).getReg .x10) answer)).mem =
      (writeBits initial destination answer).mem := by
  rw [ready_memory, (commit_setup_registers initial).2.2.2.1, pointer]
  exact write_bits_memory_congr _ _ _ answer (setup_memory _)

private theorem initial_heap_pointer (candidate : Submission) (message : Message) :
    (candidate.initialState .commit message).getReg .x12 =
      BitVec.ofNat 64 candidate.layout.trapdoor := rfl

/-- Setup changes registers only; the random syscall writes exactly the salt buffer. -/
theorem commit_input_memory (message : Message) {bits : Nat} (answer : BitVec bits) :
    (commitInputReady message answer).mem =
      (writeBits (submission.initialState .commit message) (BitVec.ofNat 64 5368713248) answer).mem := by
  apply initialized_memory
  rw [initial_heap_pointer]
  rfl

/-- Random salt generation leaves all original message blocks intact. -/
theorem commit_ready_message_block (message : Message) (answer : BitVec (256*LENGTH))
    (index : Index) (block : Nat) (inside : block < 8) :
    readBuffer (commitInputReady message answer) (4096+256*index.val+32*block) 32 =
      (message index).extractLsb' (256*block) 256 := by
  have indexBound : index.val < 2^24 := index.isLt
  rw [read_buffer_memory_congr _ _ (commit_input_memory message answer)]
  rw [write_bits_read_outside _ answer 5368713248 _ 32 (by decide)
    (by omega) (Or.inl (by omega))]
  exact commit_input_block message index block inside

/-- Each sampled 256-bit salt occupies its designated digest slot. -/
theorem commit_ready_salt (message : Message) (answer : BitVec (256*LENGTH))
    (index : Index) :
    readBuffer (commitInputReady message answer) (5368713248+32*index.val) 32 =
      answer.extractLsb' (256*index.val) 256 := by
  have indexBound : index.val < 2^24 := index.isLt
  rw [read_buffer_memory_congr _ _ (commit_input_memory message answer)]
  have written := write_bits_digest (submission.initialState .commit message) 5368713248
    (32*index.val) answer (by change 32*index.val+32 ≤ 536870912; omega) (by decide)
  simpa only [← Nat.mul_assoc, Nat.reduceMul] using written

attribute [local irreducible] commitLeaves commitInputReady checkEvaluation

/-- After all 2^24 actual leaf iterations, each heap leaf is the salted digest of
that exact input entry, for every message, salt reply, and compression oracle. -/
theorem commit_input_leaf_heap (oracle : Oracle) (message : Message)
    (answer : BitVec (256*LENGTH)) (index : Index) :
    readBuffer (checkEvaluation oracle (commitLeaves (commitInputReady message answer) LENGTH)).1
      (4831842336+32*index.val) 32 =
        leafDigest oracle.compression (answer.extractLsb' (256*index.val) 256) (message index) := by
  let wrap (i : Nat) : Index := ⟨i % LENGTH, Nat.mod_lt _ (by decide)⟩
  have wrapped (i : Nat) (inside : i < LENGTH) : (wrap i).val = i := Nat.mod_eq_of_lt inside
  have regs := commit_input_registers message answer
  have result := commit_leaves_digests oracle (commitInputReady message answer)
    4064 4831842336 5368713248 LENGTH (fun i => message (wrap i))
    (fun i => answer.extractLsb' (256*i) 256)
    regs.1 regs.2.2.2.2.1 regs.2.2.1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by
      intro i hi block hb
      have loaded := commit_ready_message_block message answer (wrap i) block hb
      rw [wrapped i hi] at loaded
      rw [show 4064+32+256*i+32*block = 4096+256*i+32*block by omega]
      exact loaded)
    (by
      intro i hi
      have loaded := commit_ready_salt message answer (wrap i)
      rw [wrapped i hi] at loaded
      exact loaded)
    index.val index.isLt
  have same : wrap index.val = index := Fin.ext (wrapped index.val index.isLt)
  simpa only [same] using result

private theorem parent_start_heap (state : MachineState) :
    (commitParentsStartState state).getReg .x9 = state.getReg .x9 := rfl

private theorem parent_start_counter (state : MachineState) :
    (commitParentsStartState state).getReg .x20 = state.getReg .x19-1 := rfl

private theorem parent_start_memory (state : MachineState) :
    (commitParentsStartState state).mem = state.mem := rfl

/-- The actual leaf and parent loops together construct a consistent heap whose
leaves are the salted input digests. No hypothesis about heap contents is required. -/
theorem commit_input_tree (oracle : Oracle) (message : Message) (answer : BitVec (256*LENGTH)) :
    let leaves := (checkEvaluation oracle (commitLeaves (commitInputReady message answer) LENGTH)).1
    let finished := (checkEvaluation oracle (commitParents (commitParentsStartState leaves) (LENGTH-1))).1
    HeapParents oracle.compression finished 4294971424 LENGTH 0 ∧
      ∀ index : Index, heapDigest finished 4294971424 (LENGTH+index.val) =
        leafDigest oracle.compression (answer.extractLsb' (256*index.val) 256) (message index) := by
  let ready := commitInputReady message answer
  let leaves := (checkEvaluation oracle (commitLeaves ready LENGTH)).1
  let parents := commitParentsStartState leaves
  have input := commit_input_registers message answer
  have leafRegs := (commit_leaves_finished ready LENGTH (commit_input_leaves message answer) leaves
    (check_evaluation_support oracle _)).2
  have parentHeap : parents.getReg .x9 = BitVec.ofNat 64 4294971424 := by
    exact (parent_start_heap leaves).trans ((leafRegs .x9 (by simp)).trans input.2.1)
  have parentCounter : parents.getReg .x20 = BitVec.ofNat 64 (LENGTH-1) := by
    rw [parent_start_counter, leafRegs .x19 (by simp), input.2.2.2.1]
    rfl
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
    rw [read_buffer_memory_congr _ _ (parent_start_memory leaves), address]
    exact commit_input_leaf_heap oracle message answer index

/-- Every path through that constructed heap reconstructs the root from the
corresponding salted input leaf. -/
theorem commit_input_tree_reconstruct (oracle : Oracle) (message : Message)
    (answer : BitVec (256*LENGTH)) (index : Index) :
    let leaves := (checkEvaluation oracle (commitLeaves (commitInputReady message answer) LENGTH)).1
    let finished := (checkEvaluation oracle (commitParents (commitParentsStartState leaves) (LENGTH-1))).1
    climb oracle.compression
      (leafDigest oracle.compression (answer.extractLsb' (256*index.val) 256) (message index))
      (heapPath (heapDigest finished 4294971424) (LENGTH+index.val) LOG_LENGTH) =
        heapDigest finished 4294971424 1 := by
  have tree := commit_input_tree oracle message answer
  dsimp only
  rw [← tree.2 index]
  exact reconstruct_heap_root oracle.compression _ LOG_LENGTH index.val index.isLt tree.1

end CommitGolfCandidate
