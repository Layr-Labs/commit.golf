import CommitGolfCandidate.CommitHeap
import CommitGolfCandidate.CommitRuntime
import CommitGolfCandidate.CommitRefinement

/-! The returned commitment and private state of the actual commitment program. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- The final eight-instruction copy returns exactly the heap root. -/
theorem commit_output_root (state : MachineState) (base output : Nat)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 output)
    (heapAligned : base % 8 = 0) (outputAligned : output % 8 = 0)
    (bounded : base+64 ≤ 2^64) (separated : output+32 ≤ base) :
    readBuffer (commitExitState (commitCopyState state 79)) output 32 = heapDigest state base 1 := by
  change readBuffer (commitCopyState state 79) output 32 = readBuffer state (base+32*1) 32
  apply commit_copy_digest state 79 (base+32) output (by simp)
  · simp only [show (79 : Nat) ≠ 46 by decide, show (79 : Nat) ≠ 55 by decide, ite_false]
    rw [heapPointer, BitVec.ofNat_add]
    rfl
  · exact outputPointer
  · omega
  · exact outputAligned
  · omega
  · omega
  · exact Or.inr (by omega)

/-- Returning the commitment preserves every 32-byte buffer above it. -/
theorem commit_output_preserves_digest (state : MachineState) (output address : Nat)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 output)
    (aligned : address % 8 = 0) (bounded : address+32 ≤ 2^64)
    (separated : output+32 ≤ address) :
    readBuffer (commitExitState (commitCopyState state 79)) address 32 = readBuffer state address 32 := by
  change readBuffer (commitCopyState state 79) address 32 = _
  exact commit_copy_preserves_digest state 79 output address (by simp) outputPointer aligned
    (by omega) bounded (Or.inr separated)

/-- Returning the commitment preserves every 16-byte buffer above it. -/
theorem commit_output_preserves_nonce (state : MachineState) (output address : Nat)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 output)
    (aligned : address % 8 = 0) (bounded : address+32 ≤ 2^64)
    (separated : output+32 ≤ address) :
    readBuffer (commitExitState (commitCopyState state 79)) address 16 = readBuffer state address 16 := by
  have left := read_buffer_slice (commitExitState (commitCopyState state 79)) address 32 0 16 (by omega)
  have right := read_buffer_slice state address 32 0 16 (by omega)
  rw [Nat.add_zero] at left right
  rw [← left, ← right, commit_output_preserves_digest state output address outputPointer aligned bounded
    separated]

/-- Evaluate the full post-randomness body through its leaf phase, parent sweep and return. -/
theorem commit_body_evaluation (oracle : Oracle) (state : MachineState) (groups : Nat) :
    checkEvaluation oracle (s3CommitBody state groups) =
      let leaves := checkEvaluation oracle (s3Leaves state groups)
      let parents := checkEvaluation oracle (s6Parents leaves.1)
      (commitExitState (commitCopyState parents.1 79), leaves.2+parents.2) := by
  -- Sequencing lemmas over variable computations only: the kernel never has to reduce the
  -- evaluation of the leaf phase to a pair.
  apply Prod.ext
  · rw [s3CommitBody, s3_evaluation_state, s3_evaluation_state, s3_evaluation_pure_state]
  · rw [s3CommitBody, s3_evaluation_calls, s3_evaluation_calls, s3_evaluation_pure_calls,
      Nat.add_zero]

/-- The 16-byte nonce of leaf `index` in a returned private state. -/
def committedNonce (state : MachineState) (index : Index) : Nonce128 :=
  readBuffer state (6106911008 + 16 * index.val) 16

/-- Contents needed to authenticate every honest opening: the returned commitment is heap node 1;
heap nodes `1 .. 2^23 - 1` are the tree of the message under the retained nonces (tagged); each
cell holds its four leaf digests. -/
def CommittedState (oracle : Oracle) (message : Message) (state : MachineState) : Prop :=
  readBuffer state 4294971392 32 = heapDigest state 4294971424 1 ∧
  (∀ node, 0 < node → node < 2 ^ 23 → heapDigest state 4294971424 node =
    s6Heap oracle.compression oracle.permutation message (expandTaggedVector (committedNonce state)) node) ∧
  ∀ index : Index, readBuffer state (4563407136 + 368 * (index.val / 4) + 72 + 32 * (index.val % 4)) 32 =
    s3LeafDigest oracle.permutation (expandTaggedVector (committedNonce state) index) (message index)

/-- Returning the root preserves the complete authentication invariant. -/
theorem commit_output_matches (oracle : Oracle) (message : Message) (state : MachineState)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 4294971424)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 4294971392)
    (heap : ∀ node, 0 < node → node < 2 ^ 23 → heapDigest state 4294971424 node =
      s6Heap oracle.compression oracle.permutation message (expandTaggedVector (committedNonce state)) node)
    (cells : ∀ index : Index,
      readBuffer state (4563407136 + 368 * (index.val / 4) + 72 + 32 * (index.val % 4)) 32 =
        s3LeafDigest oracle.permutation (expandTaggedVector (committedNonce state) index) (message index)) :
    CommittedState oracle message (commitExitState (commitCopyState state 79)) := by
  let finished := commitExitState (commitCopyState state 79)
  have nonces : committedNonce finished = committedNonce state := by
    funext index
    have indexBound : index.val < 2^24 := index.isLt
    exact commit_output_preserves_nonce state 4294971392 _ outputPointer (by omega) (by omega) (by omega)
  have preserved (node : Nat) (below : node < 2^23) :
      heapDigest finished 4294971424 node = heapDigest state 4294971424 node := by
    unfold heapDigest
    exact commit_output_preserves_digest state 4294971392 (4294971424+32*node) outputPointer
      (by omega) (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [commit_output_root state 4294971424 4294971392 heapPointer outputPointer
      (by decide) (by decide) (by decide) (by decide)]
    exact (preserved 1 (by decide)).symm
  · intro node positive below
    rw [preserved node below, nonces]
    exact heap node positive below
  · intro index
    have indexBound : index.val < 2^24 := index.isLt
    rw [nonces, commit_output_preserves_digest state 4294971392 _ outputPointer (by omega) (by omega)
      (by omega)]
    exact cells index

attribute [local irreducible] s3CommitBody s3Leaves s6Parents s3CommitReady checkEvaluation

private theorem ready_output (message : Message) {bits : Nat} (answer : BitVec bits) :
    (s3CommitReady message answer).getReg .x26 = BitVec.ofNat 64 4294971392 :=
  (s3_ready_registers message answer).2.2.2.2.2.2.2

private theorem ready_heap (message : Message) {bits : Nat} (answer : BitVec bits) :
    (s3CommitReady message answer).getReg .x9 = BitVec.ofNat 64 4294971424 :=
  (s3_ready_registers message answer).2.2.2.2.2.1

/-- The nonces of the swept state are the generated ones. -/
private theorem swept_nonces (oracle : Oracle) (message : Message) (answer : BitVec 256) :
    committedNonce (checkEvaluation oracle
      (s6Parents (checkEvaluation oracle (s3Leaves (s3CommitReady message answer) (2^18))).1)).1 =
      s4GenNonce oracle.permutation answer := by
  funext index
  exact commit_input_tree_nonce oracle message answer index

/-- The complete post-randomness body produces a returned root and private state that
authenticate the original message, for every possible seed. -/
theorem commit_body_matches (oracle : Oracle) (message : Message) (answer : BitVec 256) :
    CommittedState oracle message
      (checkEvaluation oracle (s3CommitBody (s3CommitReady message answer) (2^18))).1 := by
  let ready := s3CommitReady message answer
  let leaves := (checkEvaluation oracle (s3Leaves ready (2^18))).1
  let finished := (checkEvaluation oracle (s6Parents leaves)).1
  have heap : finished.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (s6_parents_evaluation_register oracle leaves .x9 (by decide)).trans
      ((s3_leaves_register oracle ready (2^18) .x9 (by simp)).trans (ready_heap message answer))
  have output : finished.getReg .x26 = BitVec.ofNat 64 4294971392 :=
    (s6_parents_evaluation_register oracle leaves .x26 (by decide)).trans
      ((s3_leaves_register oracle ready (2^18) .x26 (by simp)).trans (ready_output message answer))
  have nonces : committedNonce finished = s4GenNonce oracle.permutation answer :=
    swept_nonces oracle message answer
  rw [commit_body_evaluation]
  apply commit_output_matches oracle message finished heap output
  · intro node positive below
    rw [nonces]
    exact commit_input_tree oracle message answer node positive below
  · intro index
    rw [nonces]
    exact commit_input_tree_cell oracle message answer index

/-- The returned private state retains exactly the generated nonces. -/
theorem commit_body_nonce (oracle : Oracle) (message : Message) (answer : BitVec 256) (index : Index) :
    committedNonce (checkEvaluation oracle
      (s3CommitBody (s3CommitReady message answer) (2^18))).1 index =
      s4GenNonce oracle.permutation answer index := by
  let ready := s3CommitReady message answer
  let leaves := (checkEvaluation oracle (s3Leaves ready (2^18))).1
  let finished := (checkEvaluation oracle (s6Parents leaves)).1
  have output : finished.getReg .x26 = BitVec.ofNat 64 4294971392 :=
    (s6_parents_evaluation_register oracle leaves .x26 (by decide)).trans
      ((s3_leaves_register oracle ready (2^18) .x26 (by simp)).trans (ready_output message answer))
  have indexBound : index.val < 2^24 := index.isLt
  rw [commit_body_evaluation]
  unfold committedNonce
  rw [commit_output_preserves_nonce finished 4294971392 _ output (by omega) (by omega) (by omega)]
  exact commit_input_tree_nonce oracle message answer index

end CommitGolfCandidate
