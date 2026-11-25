import CommitGolfCandidate.LeafHeap
import CommitGolfCandidate.ChainRefinement
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
    (destination : Word) (pointer : initial.getReg .x12+1610612736 = destination) :
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
      (writeBits (submission.initialState .commit message) (BitVec.ofNat 64 5905584160) answer).mem := by
  apply initialized_memory
  rw [initial_heap_pointer]
  rfl

/-- Random salt generation leaves all original message blocks intact. -/
theorem commit_ready_message_block (message : Message) (answer : BitVec (256*LENGTH))
    (index : Index) (block : Nat) (inside : block < 4) :
    readBuffer (commitInputReady message answer) (4096+256*index.val+64*block) 64 =
      (message index).extractLsb' (512*block) 512 := by
  have indexBound : index.val < 2^24 := index.isLt
  rw [read_buffer_memory_congr _ _ (commit_input_memory message answer)]
  rw [write_bits_read_outside _ answer 5905584160 _ 64 (by decide)
    (by omega) (Or.inl (by omega))]
  exact commit_input_block message index block inside

/-- Each sampled 256-bit salt occupies its designated digest slot. -/
theorem commit_ready_salt (message : Message) (answer : BitVec (256*LENGTH))
    (index : Index) :
    readBuffer (commitInputReady message answer) (5905584160+32*index.val) 32 =
      answer.extractLsb' (256*index.val) 256 := by
  have indexBound : index.val < 2^24 := index.isLt
  rw [read_buffer_memory_congr _ _ (commit_input_memory message answer)]
  have written := write_bits_digest (submission.initialState .commit message) 5905584160
    (32*index.val) answer (by change 32*index.val+32 ≤ 536870912; omega) (by decide)
  simpa only [← Nat.mul_assoc, Nat.reduceMul] using written

/-- Every pair gap of the gap heap is zero before the loops: it lies above the message
vector and below the salts. -/
theorem commit_ready_gap (message : Message) (answer : BitVec (256*LENGTH)) (q : Nat)
    (inside : q < LENGTH) :
    readBuffer (commitInputReady message answer) (4294971424+96*q+64) 32 = 0 := by
  have qBound : q < 2^24 := inside
  rw [read_buffer_memory_congr _ _ (commit_input_memory message answer)]
  rw [write_bits_read_outside _ answer 5905584160 _ 32 (by decide) (by omega) (Or.inl (by omega))]
  exact commit_input_zero_digest message _ (by omega) (by omega)

theorem heap_offset_leaf (i : Nat) : heapOffset (LENGTH + i) = 805306368 + heapOffset i := by
  change heapOffset (16777216 + i) = _
  unfold heapOffset; omega

attribute [local irreducible] commitLeaves commitInputReady checkEvaluation

/-- The leaf loop never writes a pair gap. -/
theorem commit_leaves_gap (oracle : Oracle) (message : Message) (answer : BitVec (256*LENGTH))
    (q : Nat) (inside : q < LENGTH) :
    readBuffer (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/2))).1
      (4294971424+96*q+64) 32 = 0 := by
  have hL : LENGTH = 16777216 := rfl
  have qBound : q < 2^24 := inside
  have regs := commit_input_registers message answer
  rw [commit_leaves_preserves_digest oracle (commitInputReady message answer) 4064 5905584160
    5100277792 (LENGTH/2) (4294971424+96*q+64) regs.1 regs.2.2.1 regs.2.2.2.1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
    (Or.inr (by rw [hL]; omega)) (by intro p hp; rw [hL] at hp; omega)]
  exact commit_ready_gap message answer q inside

/-- After all 2^23 actual leaf-pair iterations, each heap leaf is the salted digest of
that exact input entry, for every message, salt reply, and compression oracle. -/
theorem commit_input_leaf_heap (oracle : Oracle) (message : Message)
    (answer : BitVec (256*LENGTH)) (index : Index) :
    readBuffer (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/2))).1
      (5100277792+heapOffset index.val) 32 =
        leafDigest oracle.compression (answer.extractLsb' (256*index.val) 256) (message index) := by
  let wrap (i : Nat) : Index := ⟨i % LENGTH, Nat.mod_lt _ (by decide)⟩
  have wrapped (i : Nat) (inside : i < LENGTH) : (wrap i).val = i := Nat.mod_eq_of_lt inside
  have regs := commit_input_registers message answer
  have result := commit_leaves_digests oracle (commitInputReady message answer)
    4064 5100277792 5905584160 (LENGTH/2) (fun i => message (wrap i))
    (fun i => answer.extractLsb' (256*i) 256)
    regs.1 regs.2.2.2.1 regs.2.2.1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by
      intro i hi block hb
      have loaded := commit_ready_message_block message answer (wrap i) block hb
      rw [wrapped i (by change i < 16777216; change i < 2*(16777216/2) at hi; omega)] at loaded
      rw [show 4064+32+256*i+64*block = 4096+256*i+64*block by omega]
      exact loaded)
    (by
      intro i hi
      have loaded := commit_ready_salt message answer (wrap i)
      rw [wrapped i (by change i < 16777216; change i < 2*(16777216/2) at hi; omega)] at loaded
      exact loaded)
    index.val (by have := index.isLt; change index.val < 16777216 at this; change index.val < 2*(16777216/2); omega)
  have same : wrap index.val = index := Fin.ext (wrapped index.val index.isLt)
  simpa only [same] using result

/-- The actual leaf and parent loops together construct a heap, consistent above the
cap level, whose leaves are the salted input digests. No hypothesis about heap
contents is required. -/
theorem commit_input_tree (oracle : Oracle) (message : Message) (answer : BitVec (256*LENGTH)) :
    let leaves := (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/2))).1
    let finished := (checkEvaluation oracle (commitParents (commitParentsStartState leaves) (LENGTH/2-64))).1
    HeapParents oracle.compression finished 4294971424 LENGTH 127 ∧
      ∀ index : Index, heapDigest finished 4294971424 (LENGTH+index.val) =
        leafDigest oracle.compression (answer.extractLsb' (256*index.val) 256) (message index) := by
  let ready := commitInputReady message answer
  let leaves := (checkEvaluation oracle (commitLeaves ready (LENGTH/2))).1
  let parents := commitParentsStartState leaves
  have hL : LENGTH = 16777216 := rfl
  have input := commit_input_registers message answer
  have invariant : CommitLeavesInvariant ready (LENGTH/2) := by
    rw [show LENGTH/2 = 2^23 by rw [hL]; norm_num]; exact commit_input_leaves message answer
  have leafDone := commit_leaves_finished ready (LENGTH/2) invariant leaves
    (check_evaluation_support oracle _)
  have start := commit_parents_start_state leaves leafDone.1
  have x9leaves : leaves.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (leafDone.2 .x9 (by simp)).trans input.2.1
  have pointers : ParentPointers parents 4294971424 (LENGTH/2-64) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [start.2.2.2.2.2 .x9 (by decide) (by decide) (by decide) (by decide)]; exact x9leaves
    · rw [start.1, x9leaves]; rfl
    · rw [start.2.1, x9leaves]; rfl
    · rw [start.2.2.1, x9leaves]; rfl
  have size : 2*(LENGTH/2-64+63)+2 = LENGTH := by rw [hL]
  constructor
  · have heap := commit_parents_heap oracle parents 4294971424 (LENGTH/2-64) pointers (by decide)
      (by rw [size, hL]; decide)
      (fun q _ high => by
        rw [read_buffer_memory_congr _ _ start.2.2.2.2.1]
        exact commit_leaves_gap oracle message answer q (by rw [size] at high; exact high))
    rw [size] at heap
    exact heap
  · intro index
    have indexBound : index.val < 2^24 := index.isLt
    have offsetBound := heap_offset_bound index.val (2^23) (by omega)
    change heapDigest (checkEvaluation oracle (commitParents parents (LENGTH/2-64))).1
      4294971424 (LENGTH+index.val) = _
    rw [commit_parents_preserves_digest oracle parents 4294971424 (LENGTH/2-64)
      (LENGTH+index.val) pointers (by rw [hL]; decide)
      (by change 2*(16777216/2-64+63)+1 < 16777216 + index.val; omega)
      (by rw [heap_offset_leaf]; omega)]
    have address : 4294971424+heapOffset (LENGTH+index.val) = 5100277792+heapOffset index.val := by
      rw [heap_offset_leaf]; omega
    unfold heapDigest
    rw [read_buffer_memory_congr _ _ start.2.2.2.2.1, address]
    exact commit_input_leaf_heap oracle message answer index

end CommitGolfCandidate
