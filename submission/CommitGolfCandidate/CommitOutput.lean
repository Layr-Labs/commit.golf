import CommitGolfCandidate.CommitHeap
import CommitGolfCandidate.CommitRuntime
import CommitGolfCandidate.CommitRefinement

/-! The returned commitment and private heap of the actual stage-3 commitment program. -/
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

/-- Returning the commitment preserves every digest in the private heap and nonces. -/
theorem commit_output_preserves_digest (state : MachineState) (output address : Nat)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 output)
    (aligned : address % 8 = 0) (bounded : address+32 ≤ 2^64)
    (separated : output+32 ≤ address) :
    readBuffer (commitExitState (commitCopyState state 79)) address 32 = readBuffer state address 32 := by
  change readBuffer (commitCopyState state 79) address 32 = _
  exact commit_copy_preserves_digest state 79 output address (by simp) outputPointer aligned
    (by omega) bounded (Or.inr separated)

/-- Evaluate the full post-randomness body through its leaf phase, parent loop and return. -/
theorem commit_body_evaluation (oracle : Oracle) (state : MachineState) (groups : Nat) :
    checkEvaluation oracle (s3CommitBody state groups) =
      let leaves := checkEvaluation oracle (s3Leaves state groups)
      let parents := checkEvaluation oracle
        (commitParents (commitParentsStartState leaves.1) (64*groups-1))
      (commitExitState (commitCopyState parents.1 79), leaves.2+parents.2) := by
  rw [s3CommitBody, check_evaluation_bind]
  simp only [check_evaluation_bind, check_evaluation_pure, Nat.add_zero]

/-- Contents needed to authenticate every honest opening. The root is the returned
commitment; the nonces and heap are exactly the private memory returned as trapdoor. -/
def CommittedState (oracle : Oracle) (message : Message) (state : MachineState) : Prop :=
  readBuffer state 4294971392 32 = heapDigest state 4294971424 1 ∧
  HeapParents oracle.compression state 4294971424 LENGTH 0 ∧
  ∀ index : Index, heapDigest state 4294971424 (LENGTH+index.val) =
    s3LeafDigest oracle.permutation (readNonce state (5368713248+24*index.val)) (message index)

private theorem parents_start_heap (state : MachineState) :
    (commitParentsStartState state).getReg .x9 = state.getReg .x9 :=
  commit_parents_start_register state .x9 (by simp)

private theorem parents_start_output (state : MachineState) :
    (commitParentsStartState state).getReg .x26 = state.getReg .x26 :=
  commit_parents_start_register state .x26 (by simp)

private theorem parents_start_memory (state : MachineState) :
    (commitParentsStartState state).mem = state.mem := commit_parents_start_memory state

private theorem ready_heap (message : Message) {bits : Nat} (answer : BitVec bits) :
    (s3CommitReady message answer).getReg .x9 = BitVec.ofNat 64 4294971424 :=
  (s3_ready_register message answer .x9 (by decide)).trans (commit_input_registers message answer).2.1

private theorem ready_total (message : Message) {bits : Nat} (answer : BitVec bits) :
    (s3CommitReady message answer).getReg .x19 = BitVec.ofNat 64 LENGTH :=
  (s3_ready_register message answer .x19 (by decide)).trans
    (commit_input_registers message answer).2.2.2.1

private theorem ready_output (message : Message) {bits : Nat} (answer : BitVec bits) :
    (s3CommitReady message answer).getReg .x26 = BitVec.ofNat 64 4294971392 :=
  (s3_ready_register message answer .x26 (by decide)).trans
    (commit_input_registers message answer).2.2.2.2.2.1

attribute [local irreducible] s3CommitBody s3Leaves commitParents s3CommitReady checkEvaluation

/-- The parent loop preserves the nonce buffer left by the leaf phase. -/
theorem commit_input_tree_salt (oracle : Oracle) (message : Message)
    (answer : BitVec (192*LENGTH)) (index : Index) :
    let leaves := (checkEvaluation oracle (s3Leaves (s3CommitReady message answer) (2^18))).1
    let finished := (checkEvaluation oracle (commitParents (commitParentsStartState leaves) (LENGTH-1))).1
    readNonce finished (5368713248+24*index.val) = expandNonce192 (answer.extractLsb' (192*index.val) 192) := by
  let ready := s3CommitReady message answer
  let leaves := (checkEvaluation oracle (s3Leaves ready (2^18))).1
  let parents := commitParentsStartState leaves
  have leafRegs (reg : Reg) (member : reg ∈ [Reg.x9, .x19, .x26]) :
      leaves.getReg reg = ready.getReg reg := s3_leaves_register oracle ready (2^18) reg member
  have heap : parents.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (parents_start_heap leaves).trans ((leafRegs .x9 (by simp)).trans (ready_heap message answer))
  have counter : ParentPointerInvariant parents (LENGTH-1) := by
    apply commit_parents_start_pointers_of_count leaves LENGTH
    · exact (leafRegs .x19 (by simp)).trans (ready_total message answer)
    · decide
    · decide
  have indexBound : index.val < 2^24 := index.isLt
  dsimp only
  change readNonce (checkEvaluation oracle (commitParents parents (LENGTH-1))).1
    (5368713248+24*index.val)=_
  unfold readNonce
  rw [commit_parents_preserves_buffer oracle parents 4294971424 (LENGTH-1)
    (5368713248+24*index.val) 32 heap counter
    (by change 4294971424+32*(16777216-1+1)≤5368713248+24*index.val;omega) (by omega)]
  rw [read_buffer_memory_congr _ _ (parents_start_memory leaves)]
  exact s3_leaves_salt oracle message answer index

/-- Returning the root preserves the complete authentication invariant. -/
theorem commit_output_matches (oracle : Oracle) (message : Message) (state : MachineState)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 4294971424)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 4294971392)
    (parents : HeapParents oracle.compression state 4294971424 LENGTH 0)
    (leaves : ∀ index : Index, heapDigest state 4294971424 (LENGTH+index.val) =
      s3LeafDigest oracle.permutation (readNonce state (5368713248+24*index.val)) (message index)) :
    CommittedState oracle message (commitExitState (commitCopyState state 79)) := by
  let finished := commitExitState (commitCopyState state 79)
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
    have salts := commit_output_preserves_digest state 4294971392 (5368713248+24*index.val)
      outputPointer (by omega) (by change index.val < 16777216 at indexBound; omega) (by omega)
    unfold readNonce
    rw [salts]
    exact leaves index

private theorem parent_count : 64 * 2 ^ 18 - 1 = LENGTH - 1 := by decide

/-- The complete post-randomness body produces a returned root and private heap
that authenticate the original message, for every possible nonce reply. -/
theorem commit_body_matches (oracle : Oracle) (message : Message)
    (answer : BitVec (192*LENGTH)) :
    CommittedState oracle message
      (checkEvaluation oracle (s3CommitBody (s3CommitReady message answer) (2^18))).1 := by
  let ready := s3CommitReady message answer
  let leaves := (checkEvaluation oracle (s3Leaves ready (2^18))).1
  let parents := commitParentsStartState leaves
  let finished := (checkEvaluation oracle (commitParents parents (LENGTH-1))).1
  have leafRegs (reg : Reg) (member : reg ∈ [Reg.x9, .x19, .x26]) :
      leaves.getReg reg = ready.getReg reg := s3_leaves_register oracle ready (2^18) reg member
  have heap : parents.getReg .x9 = BitVec.ofNat 64 4294971424 :=
    (parents_start_heap leaves).trans ((leafRegs .x9 (by simp)).trans (ready_heap message answer))
  have output : parents.getReg .x26 = BitVec.ofNat 64 4294971392 :=
    (parents_start_output leaves).trans ((leafRegs .x26 (by simp)).trans (ready_output message answer))
  have counter : ParentPointerInvariant parents (LENGTH-1) := by
    apply commit_parents_start_pointers_of_count leaves LENGTH
    · exact (leafRegs .x19 (by simp)).trans (ready_total message answer)
    · decide
    · decide
  have parentRegs := (commit_parents_finished parents (LENGTH-1) (by decide) counter finished
    (check_evaluation_support oracle _)).2
  have tree := commit_input_tree oracle message answer
  rw [commit_body_evaluation, parent_count]
  apply commit_output_matches oracle message finished
    ((parentRegs .x9 (by simp)).trans heap) ((parentRegs .x26 (by simp)).trans output) tree.1
  intro index
  rw [commit_input_tree_salt oracle message answer index]
  exact tree.2 index

/-- The returned private state retains exactly the random nonce reply, including
after the final root-copy instructions. -/
theorem commit_body_salt (oracle : Oracle) (message : Message)
    (answer : BitVec (192*LENGTH)) (index : Index) :
    readNonce (checkEvaluation oracle
      (s3CommitBody (s3CommitReady message answer) (2^18))).1
      (5368713248+24*index.val) = expandNonce192 (answer.extractLsb' (192*index.val) 192) := by
  let ready := s3CommitReady message answer
  let leaves := (checkEvaluation oracle (s3Leaves ready (2^18))).1
  let parents := commitParentsStartState leaves
  let finished := (checkEvaluation oracle (commitParents parents (LENGTH-1))).1
  have leafRegs (reg : Reg) (member : reg ∈ [Reg.x9, .x19, .x26]) :
      leaves.getReg reg = ready.getReg reg := s3_leaves_register oracle ready (2^18) reg member
  have output : parents.getReg .x26 = BitVec.ofNat 64 4294971392 :=
    (parents_start_output leaves).trans ((leafRegs .x26 (by simp)).trans (ready_output message answer))
  have counter : ParentPointerInvariant parents (LENGTH-1) := by
    apply commit_parents_start_pointers_of_count leaves LENGTH
    · exact (leafRegs .x19 (by simp)).trans (ready_total message answer)
    · decide
    · decide
  have parentRegs := (commit_parents_finished parents (LENGTH-1) (by decide) counter finished
    (check_evaluation_support oracle _)).2
  have indexBound : index.val < 16777216 := index.isLt
  rw [commit_body_evaluation, parent_count]
  dsimp only
  unfold readNonce
  rw [commit_output_preserves_digest finished 4294971392 (5368713248+24*index.val)
    ((parentRegs .x26 (by simp)).trans output) (by omega) (by omega) (by omega)]
  exact commit_input_tree_salt oracle message answer index

end CommitGolfCandidate
