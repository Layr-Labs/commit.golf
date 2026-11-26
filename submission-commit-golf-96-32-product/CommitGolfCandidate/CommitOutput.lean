import CommitGolfCandidate.CommitHeap
import CommitGolfCandidate.CommitRuntime

/-! The returned commitment and private heap of the actual commitment program. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

/-- The final eight-instruction copy returns exactly the heap root. -/
theorem commit_output_root (state : MachineState) (base output : Nat)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 output)
    (heapAligned : base % 8 = 0) (outputAligned : output % 8 = 0)
    (bounded : base+64 ≤ 2^64) (separated : output+32 ≤ base) :
    readBuffer (commitExitState (commitRootCopyState state)) output 32 = heapDigest state base 1 := by
  change readBuffer (commitRootCopyState state) output 32 = readBuffer state (base+32) 32
  exact commit_root_copy_digest state (base+32) output
    (by rw [heapPointer]; exact ofNat64_add_eq base 32 (base+32) rfl) outputPointer
    (by omega) outputAligned (by omega) (by omega) (Or.inr (by omega))

/-- Returning the commitment preserves every digest in the private heap. -/
theorem commit_output_preserves_digest (state : MachineState) (output address : Nat)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 output)
    (aligned : address % 8 = 0) (bounded : address+32 ≤ 2^64)
    (separated : output+32 ≤ address) :
    readBuffer (commitExitState (commitRootCopyState state)) address 32 = readBuffer state address 32 := by
  change readBuffer (commitRootCopyState state) address 32 = _
  exact commit_root_copy_preserves_digest state output address outputPointer aligned
    (by omega) bounded (Or.inr separated)

/-- Returning the commitment preserves every 16-byte salt in the private salt buffer. -/
theorem commit_output_preserves_salt (state : MachineState) (output address : Nat)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 output)
    (aligned : address % 8 = 0) (bounded : address+16 ≤ 2^64)
    (separated : output+32 ≤ address) :
    readBuffer (commitExitState (commitRootCopyState state)) address 16 = readBuffer state address 16 := by
  change readBuffer (commitRootCopyState state) address 16 = _
  exact commit_root_copy_preserves_salt state output address outputPointer aligned
    (by omega) bounded (Or.inr separated)

/-- Evaluate the full post-randomness body through its actual two loops and return. -/
theorem commit_body_evaluation (oracle : Oracle) (state : MachineState) (count : Nat) :
    checkEvaluation oracle (commitBody state count) =
      let leaves := checkEvaluation oracle (commitLeaves state (count/32))
      let parents := checkEvaluation oracle (commitParents (commitParentsStartState leaves.1) (count/32-1))
      (commitExitState (commitRootCopyState parents.1), leaves.2+parents.2) := by
  rw [commitBody, check_evaluation_bind]
  simp only [check_evaluation_bind, check_evaluation_pure, Nat.add_zero]

/-- Contents needed to authenticate every honest opening. The root is the returned
commitment; the 16-byte salts and heap are exactly the private memory returned as trapdoor. -/
def CommittedState (oracle : Oracle) (message : Message) (state : MachineState) : Prop :=
  readBuffer state 4294971392 32 = heapDigest state 4294971424 1 ∧
  HeapParents oracle.compression state 4294971424 LENGTH 0 ∧
  ∀ index : Index, heapDigest state 4294971424 (LENGTH+index.val) =
    leafDigest oracle.compression index (readBuffer state (5905584160+16*index.val) 16) (message index)

attribute [local irreducible] commitBody commitLeaves commitParents commitInputReady checkEvaluation

/-- Loop facts at the start of the parent loop, for any state reached by the leaf loop. -/
theorem parents_start_invariant (leaves : MachineState) (pc : leaves.pc = 6420)
    (x9 : leaves.getReg .x9 = BitVec.ofNat 64 4294971424)
    (x23 : leaves.getReg .x23 = BitVec.ofNat 64 5905584160)
    (x5 : leaves.getReg .x5 = 0)
    (x11 : leaves.getReg .x11 = 96) (x13 : leaves.getReg .x13 = 0) :
    ParentLoopInvariant (commitParentsStartState leaves) 4294971424 524287 := by
  have start := commit_parents_start_state leaves pc
  refine ⟨⟨?_, ?_, ?_, start.2.1⟩, ?_, ?_, ?_, ?_, by decide, by decide⟩
  · rw [start.2.2.2.2.2 .x9 (by decide) (by decide) (by decide) (by decide)]; exact x9
  · rw [start.1, x23]; rfl
  · rw [start.2.2.1, x9]; rfl
  · rw [start.2.2.2.1]; rfl
  · rw [start.2.2.2.2.2 .x5 (by decide) (by decide) (by decide) (by decide)]; exact x5
  · rw [start.2.2.2.2.2 .x11 (by decide) (by decide) (by decide) (by decide)]; exact x11
  · rw [start.2.2.2.2.2 .x13 (by decide) (by decide) (by decide) (by decide)]; exact x13

/-- Facts of the actual leaf loop's final state. -/
theorem commit_input_leaves_done (oracle : Oracle) (message : Message) {bits : Nat}
    (answer : BitVec bits) :
    (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/32))).1.pc = 6420 ∧
    (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/32))).1.getReg .x23 =
      BitVec.ofNat 64 5905584160 ∧
    ∀ reg ∈ [Reg.x9, .x26, .x5, .x11, .x13],
      (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/32))).1.getReg reg =
        (commitInputReady message answer).getReg reg := by
  have invariant : CommitLeavesInvariant (commitInputReady message answer) (LENGTH/32) := by
    rw [show LENGTH/32 = 2^19 by rw [show LENGTH = 16777216 from rfl]; norm_num]
    exact commit_input_leaves message answer
  have done := commit_leaves_finished _ (LENGTH/32) invariant _ (check_evaluation_support oracle _)
  refine ⟨done.1, ?_, done.2.2⟩
  rw [done.2.1, (commit_input_registers message answer).2.2.2.1]
  rfl

/-- Loop facts at the start of the parent loop of the actual commitment. -/
theorem commit_input_parents_start (oracle : Oracle) (message : Message) {bits : Nat}
    (answer : BitVec bits) :
    ParentLoopInvariant (commitParentsStartState
        (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/32))).1)
        4294971424 (LENGTH/32-1) ∧
      (commitParentsStartState
        (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/32))).1).getReg .x26 =
          BitVec.ofNat 64 4294971392 ∧
      (commitParentsStartState
        (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/32))).1).mem =
        (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/32))).1.mem := by
  have input := commit_input_registers message answer
  have done := commit_input_leaves_done oracle message answer
  have start := commit_parents_start_state _ done.1
  have remaining : LENGTH/32-1 = 524287 := by rw [show LENGTH = 16777216 from rfl]
  rw [remaining]
  refine ⟨parents_start_invariant _ done.1 ((done.2.2 .x9 (by simp)).trans input.2.1)
    done.2.1
    ((done.2.2 .x5 (by simp)).trans input.2.2.2.2.2.2.1)
    ((done.2.2 .x11 (by simp)).trans input.2.2.2.2.2.2.2.1)
    ((done.2.2 .x13 (by simp)).trans input.2.2.2.2.2.2.2.2), ?_, start.2.2.2.2.1⟩
  rw [start.2.2.2.2.2 .x26 (by decide) (by decide) (by decide) (by decide)]
  exact (done.2.2 .x26 (by simp)).trans input.2.2.2.2.1

/-- Both loops preserve the sampled 16-byte salt buffer. -/
theorem commit_input_tree_salt (oracle : Oracle) (message : Message) (answer : BitVec (128*LENGTH))
    (index : Index) :
    let leaves := (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/32))).1
    let finished := (checkEvaluation oracle (commitParents (commitParentsStartState leaves) (LENGTH/32-1))).1
    readBuffer finished (5905584160+16*index.val) 16 = answer.extractLsb' (128*index.val) 128 := by
  let ready := commitInputReady message answer
  let leaves := (checkEvaluation oracle (commitLeaves ready (LENGTH/32))).1
  let parents := commitParentsStartState leaves
  have hL : LENGTH = 16777216 := rfl
  have input := commit_input_registers message answer
  have start := commit_input_parents_start oracle message answer
  have indexBound : index.val < 2^24 := index.isLt
  dsimp only
  change readBuffer (checkEvaluation oracle (commitParents parents (LENGTH/32-1))).1
    (5905584160+16*index.val) 16 = _
  rw [commit_parents_preserves oracle parents 4294971424 (LENGTH/32-1) start.1.pointers
    (by rw [hL]; decide) (5905584160+16*index.val) 16 (by omega)
    (fun node _ high => Or.inr (by
      have := heap_offset_bound node (2^23) (by change node ≤ 32*(16777216/32-1)+31 at high; omega)
      omega))]
  rw [read_buffer_memory_congr _ _ start.2.2]
  rw [commit_leaves_preserves oracle ready 4072 5905584160 5100277792 (LENGTH/32)
    (5905584160+16*index.val) 16 input.1 input.2.2.1 input.2.2.2.1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
    (Or.inr (by change 4072 + 8192*(16777216/32) ≤ _; omega))
    (by
      intro i hi
      have := heap_offset_bound i (2^23) (by rw [hL] at hi; omega)
      exact Or.inr (by omega))]
  exact commit_ready_salt message answer index

/-- Returning the root preserves the complete authentication invariant. -/
theorem commit_output_matches (oracle : Oracle) (message : Message) (state : MachineState)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 4294971424)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 4294971392)
    (parents : HeapParents oracle.compression state 4294971424 LENGTH 0)
    (leaves : ∀ index : Index, heapDigest state 4294971424 (LENGTH+index.val) =
      leafDigest oracle.compression index (readBuffer state (5905584160+16*index.val) 16) (message index)) :
    CommittedState oracle message (commitExitState (commitRootCopyState state)) := by
  let finished := commitExitState (commitRootCopyState state)
  have preserved (node : Nat) (below : node < 2*LENGTH) :
      heapDigest finished 4294971424 node = heapDigest state 4294971424 node := by
    unfold heapDigest
    have := heap_offset_bound node LENGTH below
    have offsetAligned := heap_offset_aligned node
    change heapOffset node + 32 ≤ 96*16777216 at this
    exact commit_output_preserves_digest state 4294971392 (4294971424+heapOffset node) outputPointer
      (by omega) (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [commit_output_root state 4294971424 4294971392 heapPointer outputPointer
      (by decide) (by decide) (by decide) (by decide)]
    exact (preserved 1 (by decide)).symm
  · intro node positive below
    rw [preserved node (by omega), preserved (2*node) (by omega), preserved (2*node+1) (by omega)]
    exact parents node positive below
  · intro index
    have indexBound : index.val < LENGTH := index.isLt
    rw [preserved (LENGTH+index.val) (by omega)]
    have salts := commit_output_preserves_salt state 4294971392 (5905584160+16*index.val)
      outputPointer (by omega) (by change index.val < 16777216 at indexBound; omega) (by omega)
    rw [salts]
    exact leaves index

/-- The complete post-randomness body produces a returned root and private heap
that authenticate the original message, for every possible salt reply. -/
theorem commit_body_matches (oracle : Oracle) (message : Message) (answer : BitVec (128*LENGTH)) :
    CommittedState oracle message
      (checkEvaluation oracle (commitBody (commitInputReady message answer) LENGTH)).1 := by
  let ready := commitInputReady message answer
  let leaves := (checkEvaluation oracle (commitLeaves ready (LENGTH/32))).1
  let parents := commitParentsStartState leaves
  let finished := (checkEvaluation oracle (commitParents parents (LENGTH/32-1))).1
  have start := commit_input_parents_start oracle message answer
  have parentRegs := (commit_parents_finished parents 4294971424 (LENGTH/32-1) start.1 finished
    (check_evaluation_support oracle _)).2
  have tree := commit_input_tree oracle message answer
  rw [commit_body_evaluation]
  apply commit_output_matches oracle message finished
    ((parentRegs .x9 (by simp)).trans start.1.pointers.heap) ((parentRegs .x26 (by simp)).trans start.2.1)
    tree.1
  intro index
  rw [commit_input_tree_salt oracle message answer index]
  exact tree.2 index

/-- The returned private state retains exactly the random 128-bit salt reply, including
after the final root-copy instructions. -/
theorem commit_body_salt (oracle : Oracle) (message : Message)
    (answer : BitVec (128*LENGTH)) (index : Index) :
    readBuffer (checkEvaluation oracle
      (commitBody (commitInputReady message answer) LENGTH)).1
      (5905584160+16*index.val) 16 = answer.extractLsb' (128*index.val) 128 := by
  let ready := commitInputReady message answer
  let leaves := (checkEvaluation oracle (commitLeaves ready (LENGTH/32))).1
  let parents := commitParentsStartState leaves
  let finished := (checkEvaluation oracle (commitParents parents (LENGTH/32-1))).1
  have start := commit_input_parents_start oracle message answer
  have parentRegs := (commit_parents_finished parents 4294971424 (LENGTH/32-1) start.1 finished
    (check_evaluation_support oracle _)).2
  have indexBound : index.val < 16777216 := index.isLt
  rw [commit_body_evaluation]
  dsimp only
  rw [commit_output_preserves_salt finished 4294971392 (5905584160+16*index.val)
    ((parentRegs .x26 (by simp)).trans start.2.1) (by omega) (by omega) (by omega)]
  exact commit_input_tree_salt oracle message answer index

end CommitGolfCandidate
