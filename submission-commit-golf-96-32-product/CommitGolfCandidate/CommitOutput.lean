import CommitGolfCandidate.CommitHeap
import CommitGolfCandidate.CommitRuntime

/-! The returned commitment and private heap of the actual commitment program. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

/-- The final eight-instruction copy returns exactly the final chain state. -/
theorem commit_output_root (state : MachineState) (source output : Nat)
    (sourcePointer : state.getReg .x21 = BitVec.ofNat 64 source)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 output)
    (sourceAligned : source % 8 = 0) (outputAligned : output % 8 = 0)
    (bounded : source+32 ≤ 2^64) (separated : output+32 ≤ source) :
    readBuffer (commitExitState (commitCopyState state 126)) output 32 = readBuffer state source 32 := by
  change readBuffer (commitCopyState state 126) output 32 = readBuffer state source 32
  apply commit_copy_digest state 126 source output (Or.inr (Or.inr rfl))
  · unfold commitCopyFrom
    rw [if_pos rfl]
    exact sourcePointer
  · unfold commitCopyTo
    rw [if_pos rfl]
    exact outputPointer
  · exact sourceAligned
  · exact outputAligned
  · exact bounded
  · omega
  · exact Or.inr (by omega)

/-- Returning the commitment preserves every digest in the private heap and salts. -/
theorem commit_output_preserves_digest (state : MachineState) (output address : Nat)
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 output)
    (aligned : address % 8 = 0) (bounded : address+32 ≤ 2^64)
    (separated : output+32 ≤ address) :
    readBuffer (commitExitState (commitCopyState state 126)) address 32 = readBuffer state address 32 := by
  change readBuffer (commitCopyState state 126) address 32 = _
  have destination : commitCopyTo state 126 = BitVec.ofNat 64 output := by
    unfold commitCopyTo
    rw [if_pos rfl]
    exact outputPointer
  exact commit_copy_preserves_digest state 126 output address (Or.inr (Or.inr rfl)) destination aligned
    (by omega) bounded (Or.inr separated)

/-- Evaluate the full post-randomness body through its actual three loops and return. -/
theorem commit_body_evaluation (oracle : Oracle) (state : MachineState) (count : Nat) :
    checkEvaluation oracle (commitBody state count) =
      let leaves := checkEvaluation oracle (commitLeaves state (count/2))
      let parents := checkEvaluation oracle (commitParents (commitParentsStartState leaves.1) (count/2-64))
      let chained := checkEvaluation oracle (commitChain (capStartState parents.1) 64)
      (commitExitState (commitCopyState chained.1 126), leaves.2+(parents.2+chained.2)) := by
  rw [commitBody, check_evaluation_bind]
  simp only [check_evaluation_bind, check_evaluation_pure, Nat.add_zero]

/-- Contents needed to authenticate every honest opening. The commitment is the chain
over the cap (heap slots 128..255); every node above the cap level is consistent; the
salts and heap are exactly the private memory returned as trapdoor. -/
def CommittedState (oracle : Oracle) (message : Message) (state : MachineState) : Prop :=
  readBuffer state 4294971392 32 = capRoot oracle.compression (heapCap state 4294971424) ∧
  HeapParents oracle.compression state 4294971424 LENGTH 127 ∧
  ∀ index : Index, heapDigest state 4294971424 (LENGTH+index.val) =
    leafDigest oracle.compression (readBuffer state (5905584160+32*index.val) 32) (message index)

attribute [local irreducible] commitBody commitLeaves commitParents commitChain commitInputReady checkEvaluation

/-- Loop facts at the start of the parent loop, for any state reached by the leaf loop. -/
theorem parents_start_invariant (leaves : MachineState) (pc : leaves.pc = 4432)
    (x9 : leaves.getReg .x9 = BitVec.ofNat 64 4294971424) (x5 : leaves.getReg .x5 = 0)
    (x11 : leaves.getReg .x11 = 96) (x13 : leaves.getReg .x13 = 0) :
    ParentLoopInvariant (commitParentsStartState leaves) 4294971424 8388544 := by
  have start := commit_parents_start_state leaves pc
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, by decide, by decide⟩
  · rw [start.2.2.2.2.2 .x9 (by decide) (by decide) (by decide) (by decide)]; exact x9
  · rw [start.1, x9]; rfl
  · rw [start.2.1, x9]; rfl
  · rw [start.2.2.1, x9]; rfl
  · rw [start.2.2.2.1]; rfl
  · rw [start.2.2.2.2.2 .x5 (by decide) (by decide) (by decide) (by decide)]; exact x5
  · rw [start.2.2.2.2.2 .x11 (by decide) (by decide) (by decide) (by decide)]; exact x11
  · rw [start.2.2.2.2.2 .x13 (by decide) (by decide) (by decide) (by decide)]; exact x13

/-- Facts of the actual leaf loop's final state. -/
theorem commit_input_leaves_done (oracle : Oracle) (message : Message) {bits : Nat}
    (answer : BitVec bits) :
    (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/2))).1.pc = 4432 ∧
    ∀ reg ∈ [Reg.x9, .x26, .x5, .x11, .x13],
      (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/2))).1.getReg reg =
        (commitInputReady message answer).getReg reg := by
  have invariant : CommitLeavesInvariant (commitInputReady message answer) (LENGTH/2) := by
    rw [show LENGTH/2 = 2^23 by rw [show LENGTH = 16777216 from rfl]; norm_num]
    exact commit_input_leaves message answer
  exact commit_leaves_finished _ (LENGTH/2) invariant _ (check_evaluation_support oracle _)

/-- Loop facts at the start of the parent loop of the actual commitment. -/
theorem commit_input_parents_start (oracle : Oracle) (message : Message) {bits : Nat}
    (answer : BitVec bits) :
    ParentLoopInvariant (commitParentsStartState
        (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/2))).1)
        4294971424 (LENGTH/2-64) ∧
      (commitParentsStartState
        (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/2))).1).getReg .x26 =
          BitVec.ofNat 64 4294971392 ∧
      (commitParentsStartState
        (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/2))).1).mem =
        (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/2))).1.mem := by
  have input := commit_input_registers message answer
  have done := commit_input_leaves_done oracle message answer
  have start := commit_parents_start_state _ done.1
  have remaining : LENGTH/2-64 = 8388544 := by rw [show LENGTH = 16777216 from rfl]
  rw [remaining]
  refine ⟨parents_start_invariant _ done.1 ((done.2 .x9 (by simp)).trans input.2.1)
    ((done.2 .x5 (by simp)).trans input.2.2.2.2.2.2.1) ((done.2 .x11 (by simp)).trans input.2.2.2.2.2.2.2.1)
    ((done.2 .x13 (by simp)).trans input.2.2.2.2.2.2.2.2), ?_, start.2.2.2.2.1⟩
  rw [start.2.2.2.2.2 .x26 (by decide) (by decide) (by decide) (by decide)]
  exact (done.2 .x26 (by simp)).trans input.2.2.2.2.1

/-- Register and memory facts linking the parent loop, the cap start and the chain. -/
theorem commit_input_chain_facts (oracle : Oracle) (message : Message) (answer : BitVec (256*LENGTH)) :
    let leaves := (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/2))).1
    let parents := (checkEvaluation oracle (commitParents (commitParentsStartState leaves) (LENGTH/2-64))).1
    let chained := (checkEvaluation oracle (commitChain (capStartState parents) 64)).1
    ChainLoopInvariant (capStartState parents) 4294971424 64 ∧
    (capStartState parents).mem = parents.mem ∧
    chained.getReg .x21 = BitVec.ofNat 64 (4294971424 + 12256) ∧
    chained.getReg .x26 = BitVec.ofNat 64 4294971392 := by
  intro leaves parents chained
  have start := commit_input_parents_start oracle message answer
  have parentDone := commit_parents_finished (commitParentsStartState leaves) 4294971424 (LENGTH/2-64)
    start.1 parents (check_evaluation_support oracle _)
  have capPC : parents.pc = 4560 := by rw [parentDone.1.pc]; rfl
  have capStart := cap_start_state parents capPC
  have chainStart := cap_start_invariant parents 4294971424 parentDone.1 (by decide)
  have chainDone := commit_chain_finished (capStartState parents) 4294971424 64 chainStart chained
    (check_evaluation_support oracle _)
  refine ⟨chainStart, capStart.2.2.2.1, ?_, ?_⟩
  · rw [chainDone.1.pointer]
  · rw [chainDone.2 .x26 (by simp), capStart.2.2.2.2 .x26 (by decide) (by decide),
      parentDone.2 .x26 (by simp)]
    exact start.2.1

/-- The parent loop and the chain preserve every byte outside the heap's parent
slots above the cap and the chain gaps; in particular every salt and leaf. -/
theorem commit_input_stages_preserve (oracle : Oracle) (message : Message) (answer : BitVec (256*LENGTH))
    (address count : Nat) (readBound : address + count ≤ 2^64)
    (outsideNodes : ∀ node, 128 ≤ node → node < LENGTH →
      address + count ≤ 4294971424 + heapOffset node ∨ 4294971424 + heapOffset node + 32 ≤ address)
    (outsideGaps : ∀ q, 64 ≤ q → q < 128 →
      address + count ≤ 4294971424 + 96*q + 64 ∨ 4294971424 + 96*q + 96 ≤ address) :
    let leaves := (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/2))).1
    let parents := (checkEvaluation oracle (commitParents (commitParentsStartState leaves) (LENGTH/2-64))).1
    let chained := (checkEvaluation oracle (commitChain (capStartState parents) 64)).1
    readBuffer chained address count = readBuffer leaves address count := by
  intro leaves parents chained
  have hL : LENGTH = 16777216 := rfl
  have start := commit_input_parents_start oracle message answer
  have facts := commit_input_chain_facts oracle message answer
  rw [commit_chain_preserves oracle (capStartState parents) 4294971424 64 facts.1.pointer (by decide)
    (by decide) address count readBound outsideGaps]
  rw [read_buffer_memory_congr _ _ facts.2.1]
  change readBuffer (checkEvaluation oracle (commitParents (commitParentsStartState leaves) (LENGTH/2-64))).1
    address count = _
  rw [commit_parents_preserves oracle _ 4294971424 (LENGTH/2-64) start.1.pointers
    (by rw [hL]; decide) address count readBound
    (fun node low high => outsideNodes node low (by rw [hL] at high ⊢; omega))]
  exact read_buffer_memory_congr _ _ start.2.2 address count

/-- Both loops, the chain and the final return preserve the sampled salt buffer. -/
theorem commit_input_tree_salt (oracle : Oracle) (message : Message) (answer : BitVec (256*LENGTH))
    (index : Index) :
    let leaves := (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/2))).1
    let parents := (checkEvaluation oracle (commitParents (commitParentsStartState leaves) (LENGTH/2-64))).1
    let chained := (checkEvaluation oracle (commitChain (capStartState parents) 64)).1
    readBuffer chained (5905584160+32*index.val) 32 = answer.extractLsb' (256*index.val) 256 := by
  intro leaves parents chained
  have hL : LENGTH = 16777216 := rfl
  have input := commit_input_registers message answer
  have indexBound : index.val < 2^24 := index.isLt
  rw [commit_input_stages_preserve oracle message answer _ 32 (by omega)
    (fun node _ high => Or.inr (by
      have := heap_offset_bound node (2^23) (by rw [hL] at high; omega)
      omega))
    (fun q _ _ => Or.inr (by omega))]
  change readBuffer (checkEvaluation oracle (commitLeaves (commitInputReady message answer) (LENGTH/2))).1
    (5905584160+32*index.val) 32 = _
  rw [commit_leaves_preserves_digest oracle (commitInputReady message answer) 4064 5905584160 5100277792
    (LENGTH/2) (5905584160+32*index.val) input.1 input.2.2.1 input.2.2.2.1
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) (by omega)
    (Or.inr (by change 4064 + 512*(16777216/2) ≤ _; omega))
    (by intro p hp; change p < 16777216/2 at hp; omega)]
  exact commit_ready_salt message answer index

/-- The cap root of a heap reads only its 128 cap slots. -/
theorem heap_cap_root_congr (compress : Compression) (s t : MachineState) (base : Nat)
    (same : ∀ node < 128, heapDigest s base (128+node) = heapDigest t base (128+node)) :
    capRoot compress (heapCap s base) = capRoot compress (heapCap t base) := by
  apply cap_congr
  intro node below
  have small : node < 128 := by change node < 2*64 at below; omega
  simp only [heapCap, if_pos small]
  exact same node small

/-- Returning the chain state preserves the complete authentication invariant. -/
theorem commit_output_matches (oracle : Oracle) (message : Message) (state : MachineState)
    (chainPointer : state.getReg .x21 = BitVec.ofNat 64 (4294971424 + 12256))
    (outputPointer : state.getReg .x26 = BitVec.ofNat 64 4294971392)
    (root : readBuffer state (4294971424 + 12256) 32 =
      capRoot oracle.compression (heapCap state 4294971424))
    (parents : HeapParents oracle.compression state 4294971424 LENGTH 127)
    (leaves : ∀ index : Index, heapDigest state 4294971424 (LENGTH+index.val) =
      leafDigest oracle.compression (readBuffer state (5905584160+32*index.val) 32) (message index)) :
    CommittedState oracle message (commitExitState (commitCopyState state 126)) := by
  let finished := commitExitState (commitCopyState state 126)
  have preserved (node : Nat) (below : node < 2*LENGTH) :
      heapDigest finished 4294971424 node = heapDigest state 4294971424 node := by
    unfold heapDigest
    have := heap_offset_bound node LENGTH below
    have offsetAligned := heap_offset_aligned node
    change heapOffset node + 32 ≤ 96*16777216 at this
    exact commit_output_preserves_digest state 4294971392 (4294971424+heapOffset node) outputPointer
      (by omega) (by omega) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [commit_output_root state (4294971424 + 12256) 4294971392 chainPointer outputPointer
      (by decide) (by decide) (by decide) (by decide), root]
    exact heap_cap_root_congr _ _ _ _ (fun node small =>
      (preserved (128+node) (by have hL : LENGTH = 16777216 := rfl; omega)).symm)
  · intro node positive below
    rw [preserved node (by omega), preserved (2*node) (by omega), preserved (2*node+1) (by omega)]
    exact parents node positive below
  · intro index
    have indexBound : index.val < LENGTH := index.isLt
    rw [preserved (LENGTH+index.val) (by omega)]
    have salts := commit_output_preserves_digest state 4294971392 (5905584160+32*index.val)
      outputPointer (by omega) (by change index.val < 16777216 at indexBound; omega) (by omega)
    rw [salts]
    exact leaves index

/-- The complete post-randomness body produces a returned commitment and private
heap that authenticate the original message, for every possible salt reply. -/
theorem commit_body_matches (oracle : Oracle) (message : Message) (answer : BitVec (256*LENGTH)) :
    CommittedState oracle message
      (checkEvaluation oracle (commitBody (commitInputReady message answer) LENGTH)).1 := by
  let ready := commitInputReady message answer
  let leaves := (checkEvaluation oracle (commitLeaves ready (LENGTH/2))).1
  let parents := (checkEvaluation oracle (commitParents (commitParentsStartState leaves) (LENGTH/2-64))).1
  let chained := (checkEvaluation oracle (commitChain (capStartState parents) 64)).1
  have hL : LENGTH = 16777216 := rfl
  have facts := commit_input_chain_facts oracle message answer
  have tree := commit_input_tree oracle message answer
  have nodeBound (node : Nat) (below : node < 2*LENGTH) : 4294971424 + heapOffset node + 32 ≤ 2^64 := by
    have := heap_offset_bound node LENGTH below; rw [hL] at this; omega
  -- the chain writes only gaps: every node of the chained heap is the parents' node
  have nodes (node : Nat) (below : node < 2*LENGTH) :
      heapDigest chained 4294971424 node = heapDigest parents 4294971424 node := by
    rw [commit_chain_preserves_digest oracle (capStartState parents) 4294971424 64 facts.1.pointer
      (by decide) (by decide) node (nodeBound node below)]
    unfold heapDigest
    exact read_buffer_memory_congr _ _ facts.2.1 _ _
  have start := commit_input_parents_start oracle message answer
  -- h0 is the zero gap of pair 63, below every parent slot and untouched by the leaves
  have current : readBuffer (capStartState parents) (4294971424 + 12256 - 96*64) 32 =
      chainPrefix oracle.compression (heapCap (capStartState parents) 4294971424) (64 - 64) := by
    rw [show 64 - 64 = 0 from rfl, chain_prefix_zero,
      show 4294971424 + 12256 - 96*64 = 4294971424 + 96*63 + 64 from rfl,
      read_buffer_memory_congr _ _ facts.2.1]
    change readBuffer (checkEvaluation oracle
      (commitParents (commitParentsStartState leaves) (LENGTH/2-64))).1 _ 32 = 0
    rw [commit_parents_preserves oracle _ 4294971424 (LENGTH/2-64) start.1.pointers
      (by rw [hL]; decide) _ 32 (by decide)
      (fun node low _ => Or.inl (by unfold heapOffset; omega)),
      read_buffer_memory_congr _ _ start.2.2]
    exact commit_leaves_gap oracle message answer 63 (by decide)
  have root := commit_chain_root oracle (capStartState parents) 4294971424 64 facts.1.pointer
    (by decide) (by decide) (by decide) current
  rw [commit_body_evaluation]
  apply commit_output_matches oracle message chained facts.2.2.1 facts.2.2.2
  · change readBuffer chained (4294971424 + 12256) 32 = _
    rw [root]
    exact heap_cap_root_congr _ _ _ _ (fun node small => by
      rw [nodes (128+node) (by rw [hL]; omega)]
      unfold heapDigest
      exact read_buffer_memory_congr _ _ facts.2.1 _ _)
  · intro node positive below
    rw [nodes node (by omega), nodes (2*node) (by omega), nodes (2*node+1) (by omega)]
    exact tree.1 node positive below
  · intro index
    have indexBound : index.val < LENGTH := index.isLt
    rw [nodes (LENGTH+index.val) (by omega), commit_input_tree_salt oracle message answer index]
    exact tree.2 index

/-- The returned private state retains exactly the random salt reply, including
after the final commitment-copy instructions. This identifies the randomness visible
in an opening without making any distributional assumption about the oracle. -/
theorem commit_body_salt (oracle : Oracle) (message : Message)
    (answer : BitVec (256*LENGTH)) (index : Index) :
    readBuffer (checkEvaluation oracle
      (commitBody (commitInputReady message answer) LENGTH)).1
      (5905584160+32*index.val) 32 = answer.extractLsb' (256*index.val) 256 := by
  have facts := commit_input_chain_facts oracle message answer
  have indexBound : index.val < 16777216 := index.isLt
  rw [commit_body_evaluation]
  dsimp only
  rw [commit_output_preserves_digest _ 4294971392 (5905584160+32*index.val)
    facts.2.2.2 (by omega) (by omega) (by omega)]
  exact commit_input_tree_salt oracle message answer index

end CommitGolfCandidate
