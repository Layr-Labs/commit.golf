import CommitGolfCandidate.CommitTree
import CommitGolfCandidate.CheckEvaluation
import CommitGolfCandidate.WriteMemory
import CommitGolfCandidate.HeapModel

/-! Contents of the actual bottom-up commitment heap. Each parent syscall reads
its two children and changes exactly one digest slot. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Digest stored at a node of the machine's heap, including its unused slot zero. -/
def heapDigest (state : MachineState) (base node : Nat) : Digest :=
  readBuffer state (base + 32 * node) 32

private theorem memory_read_congr (left right : MachineState) (same : left.mem = right.mem)
    (address count : Nat) : readBuffer left address count = readBuffer right address count := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem, same]

private theorem shifted_address (base node shift : Nat) :
    BitVec.ofNat 64 base + (BitVec.ofNat 64 node <<< shift) =
      BitVec.ofNat 64 (base + 2^shift * node) := by
  have power : BitVec.twoPow 64 shift = BitVec.ofNat 64 (2^shift) := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [BitVec.shiftLeft_eq_mul_twoPow, power, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  rw [Nat.mul_comm node]

/-- Setup and loop-control instructions leave memory alone; only the reply is stored. -/
theorem commit_parent_step_memory (state : MachineState) (answer : Digest) (base node : Nat)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (pointers : ParentPointerInvariant state node) :
    (commitParentNextState (commitParentState state answer)).mem =
      (writeBits state (BitVec.ofNat 64 (base + 32*node)) answer).mem := by
  change (commitParentState state answer).mem = _
  rw [commit_parent_written_memory, pointers.2, heapPointer, ← BitVec.ofNat_add]

/-- The written parent is exactly the compression reply, byte for byte. -/
theorem commit_parent_stored_digest (state : MachineState) (answer : Digest) (base node : Nat)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (pointers : ParentPointerInvariant state node) :
    heapDigest (commitParentNextState (commitParentState state answer)) base node = answer := by
  unfold heapDigest
  rw [memory_read_congr _ _ (commit_parent_step_memory state answer base node heapPointer pointers)]
  have written := write_bits_digest state (base+32*node) 0 answer (by decide) (by decide)
  simpa using written

/-- Writing one heap node preserves every other complete digest slot. -/
theorem commit_parent_preserves_digest (state : MachineState) (answer : Digest) (base node other : Nat)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (pointers : ParentPointerInvariant state node)
    (writeBound : base+32*node+32 ≤ 2^64) (readBound : base+32*other+32 ≤ 2^64)
    (different : other ≠ node) :
    heapDigest (commitParentNextState (commitParentState state answer)) base other =
      heapDigest state base other := by
  unfold heapDigest
  rw [memory_read_congr _ _ (commit_parent_step_memory state answer base node heapPointer pointers)]
  exact write_bits_read_outside state answer (base+32*node) (base+32*other) 32
    writeBound readBound (by omega)

/-- The parent's syscall reads the adjacent child slots in the reference byte order. -/
theorem commit_parent_query_digest (oracle : Oracle) (state : MachineState) (base node : Nat)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (pointers : ParentPointerInvariant state node)
    (aligned : base % 8 = 0) (bounded : base+64*node < 2^64) :
    oracle.answer (m := Id) (commitParentQuery state) =
      combine oracle.compression (heapDigest state base (2*node)) (heapDigest state base (2*node+1)) := by
  change oracle.compression (readBuffer state (state.getReg .x10).toNat 64) = _
  rw [pointers.1, heapPointer, ← BitVec.ofNat_add]
  change oracle.compression (readBuffer state ((base+64*node) % 2^64) 64) = _
  rw [Nat.mod_eq_of_lt bounded, read_compression_halves state _ (by omega)]
  change oracle.compression (_ ++ _) = oracle.compression (_ ++ _)
  have left : base+32*(2*node) = base+64*node := by omega
  have right : base+32*(2*node+1) = base+64*node+32 := by omega
  simp only [heapDigest, left, right]

/-- The suffix of internal nodes already constructed by the descending loop. -/
def HeapParents (compress : Compression) (state : MachineState)
    (base leaves remaining : Nat) : Prop :=
  ∀ node, remaining < node → node < leaves →
    heapDigest state base node =
      combine compress (heapDigest state base (2*node)) (heapDigest state base (2*node+1))

/-- One actual compression step extends the consistent heap suffix by one node. -/
theorem commit_parent_extends_heap (oracle : Oracle) (state : MachineState)
    (base leaves remaining : Nat)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (pointers : ParentPointerInvariant state (remaining+1))
    (aligned : base % 8 = 0) (bounded : base+64*leaves ≤ 2^64)
    (inside : remaining+1 < leaves)
    (parents : HeapParents oracle.compression state base leaves (remaining+1)) :
    HeapParents oracle.compression
      (commitParentNextState (commitParentState state
        (oracle.answer (m := Id) (commitParentQuery state)))) base leaves remaining := by
  let answer : Digest := oracle.answer (m := Id) (commitParentQuery state)
  let next := commitParentNextState (commitParentState state answer)
  have preserved (node : Nat) (inHeap : node < 2*leaves) (different : node ≠ remaining+1) :
      heapDigest next base node = heapDigest state base node :=
    commit_parent_preserves_digest state answer base (remaining+1) node heapPointer pointers
      (by omega) (by omega) different
  intro node after below
  change heapDigest next base node = combine _ (heapDigest next base (2*node)) _
  rw [preserved (2*node) (by omega) (by omega),
      preserved (2*node+1) (by omega) (by omega)]
  by_cases current : node = remaining+1
  · subst node
    rw [commit_parent_stored_digest state answer base (remaining+1) heapPointer pointers]
    exact commit_parent_query_digest oracle state base (remaining+1) heapPointer pointers aligned (by omega)
  · rw [preserved node (by omega) current]
    exact parents node (by omega) below

/-- Evaluate the public-only parent loop against the chosen oracle realization. -/
theorem commit_parents_evaluation (oracle : Oracle) (state : MachineState) (remaining : Nat) :
    checkEvaluation oracle (commitParents state (remaining+1)) =
      let next := commitParentNextState (commitParentState state
        (oracle.answer (m := Id) (commitParentQuery state)))
      let result := checkEvaluation oracle (commitParents next remaining)
      (result.1, 1+result.2) := by
  rw [commitParents, check_evaluation_public_bind]

/-- After the descending loop, every internal node agrees with its final children. -/
theorem commit_parents_consistent (oracle : Oracle) (state : MachineState)
    (base leaves remaining : Nat)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (pointers : ParentPointerInvariant state remaining)
    (aligned : base % 8 = 0) (bounded : base+64*leaves ≤ 2^64)
    (inside : remaining < leaves)
    (parents : HeapParents oracle.compression state base leaves remaining) :
    HeapParents oracle.compression
      (checkEvaluation oracle (commitParents state remaining)).1 base leaves 0 := by
  induction remaining generalizing state with
  | zero => simpa only [commitParents, check_evaluation_pure] using parents
  | succ remaining ih =>
    rw [commit_parents_evaluation]
    let answer : Digest := oracle.answer (m := Id) (commitParentQuery state)
    let next := commitParentNextState (commitParentState state answer)
    have nextPointers : ParentPointerInvariant next remaining :=
      commit_parent_step_pointers state answer remaining pointers
    exact ih next
      ((commit_parent_step_register state answer .x9 (by simp)).trans heapPointer)
      nextPointers (by omega)
      (commit_parent_extends_heap oracle state base leaves remaining heapPointer pointers aligned
        bounded inside parents)

/-- Descending parent construction never changes any leaf or other higher heap slot. -/
theorem commit_parents_preserves_digest (oracle : Oracle) (state : MachineState)
    (base remaining node : Nat)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (pointers : ParentPointerInvariant state remaining)
    (after : remaining < node) (bounded : base+32*node+32 ≤ 2^64) :
    heapDigest (checkEvaluation oracle (commitParents state remaining)).1 base node =
      heapDigest state base node := by
  induction remaining generalizing state with
  | zero => rw [commitParents, check_evaluation_pure]
  | succ remaining ih =>
    rw [commit_parents_evaluation]
    let answer : Digest := oracle.answer (m := Id) (commitParentQuery state)
    let next := commitParentNextState (commitParentState state answer)
    have nextPointers : ParentPointerInvariant next remaining :=
      commit_parent_step_pointers state answer remaining pointers
    change heapDigest (checkEvaluation oracle (commitParents next remaining)).1 base node = _
    rw [ih next ((commit_parent_step_register state answer .x9 (by simp)).trans heapPointer)
      nextPointers (by omega)]
    exact commit_parent_preserves_digest state answer base (remaining+1) node heapPointer pointers
      (by omega) bounded (by omega)

/-- Starting at the last internal node needs no assumptions about pre-existing
parent contents. The actual loop establishes all parent equations itself. -/
theorem commit_parents_heap (oracle : Oracle) (state : MachineState) (base leaves : Nat)
    (positive : 0 < leaves)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (pointers : ParentPointerInvariant state (leaves-1))
    (aligned : base % 8 = 0) (bounded : base+64*leaves ≤ 2^64) :
    HeapParents oracle.compression
      (checkEvaluation oracle (commitParents state (leaves-1))).1 base leaves 0 :=
  commit_parents_consistent oracle state base leaves (leaves-1) heapPointer pointers
    aligned bounded (by omega) (by intro node after below; omega)

/-- Every original leaf authenticates to the root constructed by the actual parent
loop, using siblings from its resulting heap. -/
theorem commit_parents_reconstruct (oracle : Oracle) (state : MachineState)
    (base depth index : Nat) (inside : index < 2^depth)
    (heapPointer : state.getReg .x9 = BitVec.ofNat 64 base)
    (pointers : ParentPointerInvariant state (2^depth-1))
    (aligned : base % 8 = 0) (bounded : base+64*2^depth ≤ 2^64) :
    let finished := (checkEvaluation oracle (commitParents state (2^depth-1))).1
    climb oracle.compression (heapDigest state base (2^depth+index))
      (heapPath (heapDigest finished base) (2^depth+index) depth) =
      heapDigest finished base 1 := by
  have positive : 0 < 2^depth := by positivity
  have parents := commit_parents_heap oracle state base (2^depth) positive
    heapPointer pointers aligned bounded
  have leaf := commit_parents_preserves_digest oracle state base (2^depth-1)
    (2^depth+index) heapPointer pointers (by omega) (by omega)
  dsimp only
  rw [← leaf]
  exact reconstruct_heap_root oracle.compression _ depth index inside parents

end CommitGolfCandidate
