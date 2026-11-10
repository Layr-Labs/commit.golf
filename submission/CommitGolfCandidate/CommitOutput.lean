import CommitGolfCandidate.CommitHeap
import CommitGolfCandidate.CommitRuntime

/-! The returned commitment and private heap of the actual commitment program. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The final eight-instruction copy returns exactly the heap root. -/
theorem commit_output_root (state : MachineState) (base output : Nat)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 output)
    (heapAligned : base % 8 = 0) (outputAligned : output % 8 = 0)
    (bounded : base+64 ≤ 2^64) (separated : output+32 ≤ base) :
    readBuffer (commitExitState (commitCopyState state 92)) output 32 = heapDigest state base 1 := by
  change readBuffer (commitCopyState state 92) output 32 = readBuffer state (base+32*1) 32
  apply commit_copy_digest state 92 (base+32) output (by simp)
  · simp only [show (92 : Nat) ≠ 46 by decide, show (92 : Nat) ≠ 55 by decide, ite_false]
    rw [heapPointer, BitVec.ofNat_add]
    rfl
  · exact outputPointer
  · omega
  · exact outputAligned
  · omega
  · omega
  · exact Or.inr (by omega)

/-- Returning the commitment preserves every digest in the private heap and salts. -/
theorem commit_output_preserves_digest (state : MachineState) (output address : Nat)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 output)
    (aligned : address % 8 = 0) (bounded : address+32 ≤ 2^64)
    (separated : output+32 ≤ address) :
    readBuffer (commitExitState (commitCopyState state 92)) address 32 = readBuffer state address 32 := by
  change readBuffer (commitCopyState state 92) address 32 = _
  exact commit_copy_preserves_digest state 92 output address (by simp) outputPointer aligned
    (by omega) bounded (Or.inr separated)

/-- Evaluate the full post-randomness body through its actual two loops and return. -/
theorem commit_body_evaluation (oracle : Oracle) (state : MachineState) (count : Nat) :
    checkEvaluation oracle (commitBody state count) =
      let leaves := checkEvaluation oracle (commitLeaves state count)
      let parents := checkEvaluation oracle (commitParents (commitParentsStartState leaves.1) (count-1))
      (commitExitState (commitCopyState parents.1 92), leaves.2+parents.2) := by
  rw [commitBody, check_evaluation_bind]
  simp only [check_evaluation_bind, check_evaluation_pure, Nat.add_zero]

/-- Contents needed to authenticate every honest opening. The root is the returned
commitment; the salts and heap are exactly the private memory returned as trapdoor. -/
def CommittedState (oracle : Oracle) (message : Message) (state : MachineState) : Prop :=
  readBuffer state 4294971392 32 = heapDigest state 4294971424 1 ∧
  HeapParents oracle.compression state 4294971424 LENGTH 0 ∧
  ∀ index : Index, heapDigest state 4294971424 (LENGTH+index.val) =
    leafDigest oracle.compression (readBuffer state (5368713248+32*index.val) 32) (message index)

private theorem parents_start_heap (state : MachineState) :
    (commitParentsStartState state).getReg .x9 = state.getReg .x9 :=
  commit_parents_start_register state .x9 (by simp)

private theorem parents_start_output (state : MachineState) :
    (commitParentsStartState state).getReg .x26 = state.getReg .x26 :=
  commit_parents_start_register state .x26 (by simp)

private theorem parents_start_counter (state : MachineState) :
    (commitParentsStartState state).getReg .x20 = state.getReg .x19-1 :=
  commit_parents_start_counter state

private theorem parents_start_memory (state : MachineState) :
    (commitParentsStartState state).mem = state.mem := rfl

attribute [local irreducible] commitBody commitLeaves commitParents commitInputReady checkEvaluation

/-- Both loops and the final return preserve the sampled salt buffer. -/
theorem commit_input_tree_salt (oracle : Oracle) (message : Message) (answer : BitVec (256*LENGTH))
    (index : Index) :
    let leaves := (checkEvaluation oracle (commitLeaves (commitInputReady message answer) LENGTH)).1
    let finished := (checkEvaluation oracle (commitParents (commitParentsStartState leaves) (LENGTH-1))).1
    readBuffer finished (5368713248+32*index.val) 32 = answer.extractLsb' (256*index.val) 256 := by
  let ready := commitInputReady message answer
  let leaves := (checkEvaluation oracle (commitLeaves ready LENGTH)).1
  let parents := commitParentsStartState leaves
  have input := commit_input_registers message answer
  have leafRegs := (commit_leaves_finished ready LENGTH (commit_input_leaves message answer) leaves
    (check_evaluation_support oracle _)).2
  have heap : parents.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (parents_start_heap leaves).trans ((leafRegs .x9 (by simp)).trans input.2.1)
  have counter : parents.getReg .x20 = BitVec.ofNat 64 (LENGTH-1) := by
    rw [parents_start_counter, leafRegs .x19 (by simp), input.2.2.2.1]
    rfl
  have indexBound : index.val < 2^24 := index.isLt
  have address : 5368713248+32*index.val = 4294971424+32*(2*LENGTH+index.val) := by
    change _ = 4294971424+32*(2*16777216+index.val)
    omega
  dsimp only
  rw [address]
  change heapDigest (checkEvaluation oracle (commitParents parents (LENGTH-1))).1
    4294971424 (2*LENGTH+index.val) = _
  rw [commit_parents_preserves_digest oracle parents 4294971424 (LENGTH-1)
    (2*LENGTH+index.val) heap counter
    (by change 16777216-1 < 2*16777216+index.val; omega)
    (by change 4294971424+32*(2*16777216+index.val)+32 ≤ 2^64; omega)]
  unfold heapDigest
  rw [read_buffer_memory_congr _ _ (parents_start_memory leaves), ← address]
  rw [commit_leaves_preserves_digest oracle ready 4096 4831842336 LENGTH (5368713248+32*index.val)
    (commit_input_leaves message answer).scratch input.1 input.2.2.2.2.1
    (by decide) (by decide) (by omega) (by decide) (by omega)
    (Or.inr (by change 4096+256*16777216 ≤ _; omega))
    (Or.inr (by change 4831842336+32*16777216 ≤ _; omega))]
  exact commit_ready_salt message answer index

/-- Returning the root preserves the complete authentication invariant. -/
theorem commit_output_matches (oracle : Oracle) (message : Message) (state : MachineState)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 4294971424)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 4294971392)
    (parents : HeapParents oracle.compression state 4294971424 LENGTH 0)
    (leaves : ∀ index : Index, heapDigest state 4294971424 (LENGTH+index.val) =
      leafDigest oracle.compression (readBuffer state (5368713248+32*index.val) 32) (message index)) :
    CommittedState oracle message (commitExitState (commitCopyState state 92)) := by
  let finished := commitExitState (commitCopyState state 92)
  have preserved (node : Nat) (below : node < 3*LENGTH) :
      heapDigest finished 4294971424 node = heapDigest state 4294971424 node := by
    unfold heapDigest
    exact commit_output_preserves_digest state 4294971392 (4294971424+32*node) outputPointer
      (by omega) (by change node < 3*16777216 at below; omega) (by omega)
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
    have salts := commit_output_preserves_digest state 4294971392 (5368713248+32*index.val)
      outputPointer (by omega) (by change index.val < 16777216 at indexBound; omega) (by omega)
    rw [salts]
    exact leaves index

/-- The complete post-randomness body produces a returned root and private heap
that authenticate the original message, for every possible salt reply. -/
theorem commit_body_matches (oracle : Oracle) (message : Message) (answer : BitVec (256*LENGTH)) :
    CommittedState oracle message
      (checkEvaluation oracle (commitBody (commitInputReady message answer) LENGTH)).1 := by
  let ready := commitInputReady message answer
  let leaves := (checkEvaluation oracle (commitLeaves ready LENGTH)).1
  let parents := commitParentsStartState leaves
  let finished := (checkEvaluation oracle (commitParents parents (LENGTH-1))).1
  have input := commit_input_registers message answer
  have leafRegs := (commit_leaves_finished ready LENGTH (commit_input_leaves message answer) leaves
    (check_evaluation_support oracle _)).2
  have heap : parents.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (parents_start_heap leaves).trans ((leafRegs .x9 (by simp)).trans input.2.1)
  have output : parents.getReg .x26 = BitVec.ofNat 64 4294971392 :=
    (parents_start_output leaves).trans ((leafRegs .x26 (by simp)).trans input.2.2.2.2.2.1)
  have counter : parents.getReg .x20 = BitVec.ofNat 64 (LENGTH-1) := by
    rw [parents_start_counter, leafRegs .x19 (by simp), input.2.2.2.1]
    rfl
  have parentRegs := (commit_parents_finished parents (LENGTH-1) (by decide) counter finished
    (check_evaluation_support oracle _)).2
  have tree := commit_input_tree oracle message answer
  rw [commit_body_evaluation]
  apply commit_output_matches oracle message finished
    ((parentRegs .x9 (by simp)).trans heap) ((parentRegs .x26 (by simp)).trans output) tree.1
  intro index
  rw [commit_input_tree_salt oracle message answer index]
  exact tree.2 index

/-- The returned private state retains exactly the random salt reply, including
after the final root-copy instructions. This identifies the randomness visible in
an opening without making any distributional assumption about the oracle. -/
theorem commit_body_salt (oracle : Oracle) (message : Message)
    (answer : BitVec (256*LENGTH)) (index : Index) :
    readBuffer (checkEvaluation oracle
      (commitBody (commitInputReady message answer) LENGTH)).1
      (5368713248+32*index.val) 32 = answer.extractLsb' (256*index.val) 256 := by
  let ready := commitInputReady message answer
  let leaves := (checkEvaluation oracle (commitLeaves ready LENGTH)).1
  let parents := commitParentsStartState leaves
  let finished := (checkEvaluation oracle (commitParents parents (LENGTH-1))).1
  have input := commit_input_registers message answer
  have leafRegs := (commit_leaves_finished ready LENGTH (commit_input_leaves message answer) leaves
    (check_evaluation_support oracle _)).2
  have output : parents.getReg .x26 = BitVec.ofNat 64 4294971392 :=
    (parents_start_output leaves).trans ((leafRegs .x26 (by simp)).trans input.2.2.2.2.2.1)
  have counter : parents.getReg .x20 = BitVec.ofNat 64 (LENGTH-1) := by
    rw [parents_start_counter, leafRegs .x19 (by simp), input.2.2.2.1]
    rfl
  have parentRegs := (commit_parents_finished parents (LENGTH-1) (by decide) counter finished
    (check_evaluation_support oracle _)).2
  have indexBound : index.val < 16777216 := index.isLt
  rw [commit_body_evaluation]
  dsimp only
  rw [commit_output_preserves_digest finished 4294971392 (5368713248+32*index.val)
    ((parentRegs .x26 (by simp)).trans output) (by omega) (by omega) (by omega)]
  exact commit_input_tree_salt oracle message answer index

end CommitGolfCandidate
