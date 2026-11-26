import CommitGolfCandidate.CommitTree
import CommitGolfCandidate.Evaluation
import CommitGolfCandidate.WriteMemory
import CommitGolfCandidate.HeapModel
import CommitGolfCandidate.HeapLayout

/-! Contents of the actual bottom-up commitment gap heap. Node `s` lives at
`base + heapOffset s`; each parent call reads the contiguous pair `[2q | 2q+1 | gap]`
and, as long as the gap is zero, its input is exactly the reference padded pair. Every
call changes exactly one node slot and never a gap. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-- Digest stored at a node of the machine's gap heap, including its unused slot zero. -/
def heapDigest (state : MachineState) (base node : Nat) : Digest :=
  readBuffer state (base + heapOffset node) 32

private theorem memory_read_congr (left right : MachineState) (same : left.mem = right.mem)
    (address count : Nat) : readBuffer left address count = readBuffer right address count := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem, same]

/-- Reply of parent call `j` under a fixed oracle. -/
def parentAnswer (oracle : Oracle) (state : MachineState) (j : Nat) : BitVec 256 :=
  oracle.compression (readBuffer state (parentSource state j).toNat 96)

/-- Parent call `j` evaluated with a fixed oracle. -/
def parentStep (oracle : Oracle) (state : MachineState) (j : Nat) : MachineState :=
  parentCallState state j (parentAnswer oracle state j)

theorem parent_iteration_evaluation (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (parentIterationRun state) =
      (parentNextState (parentStep oracle (parentStep oracle state 0) 1), 2) := by
  simp only [parentIterationRun, check_evaluation_public_bind, check_evaluation_pure]
  rfl

theorem commit_parents_evaluation_zero (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (commitParents state 0) = (state, 0) := by
  simp only [commitParents, check_evaluation_pure]

/-- Evaluate one parent iteration followed by the rest of the loop. -/
theorem commit_parents_evaluation (oracle : Oracle) (state : MachineState) (remaining : Nat) :
    checkEvaluation oracle (commitParents state (remaining+1)) =
      let next := parentNextState (parentStep oracle (parentStep oracle state 0) 1)
      let result := checkEvaluation oracle (commitParents next remaining)
      (result.1, 2+result.2) := by
  rw [commitParents, check_evaluation_bind, parent_iteration_evaluation]

theorem parent_step_register (oracle : Oracle) (state : MachineState) (j : Nat) (hj : j < 3)
    (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (parentStep oracle state j).getReg reg = state.getReg reg :=
  parent_call_register state j hj _ reg n10 n12

/-- The parent's reply is written at its output slot. -/
theorem parent_step_written (oracle : Oracle) (state : MachineState) (j out : Nat)
    (hout : (parentOutput state j).toNat = out) :
    readBuffer (parentStep oracle state j) out 32 = parentAnswer oracle state j := by
  have outWord : parentOutput state j = BitVec.ofNat 64 out := by
    rw [word_ofNat_toNat (parentOutput state j), hout]
  unfold parentStep
  rw [memory_read_congr _ _ (parent_call_memory state j _), outWord]
  have written := write_bits_digest state out 0 (parentAnswer oracle state j) (by decide) (by decide)
  simpa using written

/-- A parent call changes no byte outside its 32-byte output slot. -/
theorem parent_step_outside (oracle : Oracle) (state : MachineState) (j out : Nat)
    (hout : (parentOutput state j).toNat = out) (outBound : out + 32 ≤ 2^64)
    (address count : Nat) (readBound : address + count ≤ 2^64)
    (separate : address + count ≤ out ∨ out + 32 ≤ address) :
    readBuffer (parentStep oracle state j) address count = readBuffer state address count := by
  have outWord : parentOutput state j = BitVec.ofNat 64 out := by
    rw [word_ofNat_toNat (parentOutput state j), hout]
  unfold parentStep
  rw [memory_read_congr _ _ (parent_call_memory state j _), outWord]
  exact write_bits_read_outside state _ out address count (by simpa using outBound) readBound
    (by simpa using separate)

private theorem pad_pair (right left : BitVec 256) :
    ((0 : BitVec 256) ++ right) ++ left = padInput (right ++ left) := by
  unfold padInput
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append]
  simp

/-- The 96-byte pair `[left | right | zero gap]` is the reference padded pair. -/
theorem parent_answer_combine (oracle : Oracle) (state : MachineState) (j base q : Nat)
    (hsource : (parentSource state j).toNat = base + 96*q) (aligned : base % 8 = 0)
    (gap : readBuffer state (base + 96*q + 64) 32 = 0) :
    parentAnswer oracle state j =
      combine oracle.compression (heapDigest state base (2*q)) (heapDigest state base (2*q+1)) := by
  have alignedMid : (base + 96*q + 32) % 8 = 0 := by omega
  have h96 : readBuffer state (base + 96*q) 96 =
      (readBuffer state (base + 96*q + 32 + 32) 32 ++ readBuffer state (base + 96*q + 32) 32) ++
        readBuffer state (base + 96*q) 32 := by
    rw [read_leaf_query state (base + 96*q), read_compression_halves state (base + 96*q + 32) alignedMid]
  have e64 : base + 96*q + 32 + 32 = base + 96*q + 64 := by omega
  have eOdd : base + heapOffset (2*q+1) = base + 96*q + 32 := by rw [heap_offset_odd]; omega
  have eEven : base + heapOffset (2*q) = base + 96*q := by rw [heap_offset_even]
  have input : readBuffer state (parentSource state j).toNat 96 =
      padInput (readBuffer state (base + heapOffset (2*q+1)) 32 ++
        readBuffer state (base + heapOffset (2*q)) 32) := by
    rw [eOdd, eEven, hsource, h96, e64, gap]
    exact pad_pair _ _
  exact congrArg oracle.compression input

/-- The parent node written by a call on pair `q`. -/
theorem parent_step_node (oracle : Oracle) (state : MachineState) (j base q : Nat)
    (hsource : (parentSource state j).toNat = base + 96*q)
    (hout : (parentOutput state j).toNat = base + heapOffset q) (aligned : base % 8 = 0)
    (gap : readBuffer state (base + 96*q + 64) 32 = 0) :
    heapDigest (parentStep oracle state j) base q =
      combine oracle.compression (heapDigest state base (2*q)) (heapDigest state base (2*q+1)) := by
  show readBuffer (parentStep oracle state j) (base + heapOffset q) 32 = _
  rw [parent_step_written oracle state j _ hout]
  exact parent_answer_combine oracle state j base q hsource aligned gap

/-- Writing node `m` preserves every other node slot. -/
theorem parent_step_other_node (oracle : Oracle) (state : MachineState) (j base m node : Nat)
    (hout : (parentOutput state j).toNat = base + heapOffset m)
    (bound : base + heapOffset m + 32 ≤ 2^64) (readBound : base + heapOffset node + 32 ≤ 2^64)
    (different : node ≠ m) :
    heapDigest (parentStep oracle state j) base node = heapDigest state base node := by
  have disjoint := heap_offset_disjoint node m different
  exact parent_step_outside oracle state j _ hout bound _ 32 readBound (by omega)

/-- Writing node `m` preserves every pair gap. -/
theorem parent_step_gap (oracle : Oracle) (state : MachineState) (j base m q : Nat)
    (hout : (parentOutput state j).toNat = base + heapOffset m)
    (bound : base + heapOffset m + 32 ≤ 2^64) (readBound : base + 96*q + 96 ≤ 2^64) :
    readBuffer (parentStep oracle state j) (base + 96*q + 64) 32 =
      readBuffer state (base + 96*q + 64) 32 := by
  have gap := heap_offset_gap m q
  exact parent_step_outside oracle state j _ hout bound _ 32 (by omega) (by omega)

/-- The suffix of internal nodes already constructed by the descending loop. -/
def HeapParents (compress : Compression) (state : MachineState)
    (base leaves remaining : Nat) : Prop :=
  ∀ node, remaining < node → node < leaves →
    heapDigest state base node =
      combine compress (heapDigest state base (2*node)) (heapDigest state base (2*node+1))

/-- Computing node `m` from final children extends the consistent heap suffix. -/
theorem heap_parents_extend (compress : Compression) (state next : MachineState)
    (base leaves m : Nat) (positive : 1 ≤ m) (inside : m < leaves)
    (written : heapDigest next base m =
      combine compress (heapDigest state base (2*m)) (heapDigest state base (2*m+1)))
    (preserved : ∀ node, node ≠ m → node < 2*leaves →
      heapDigest next base node = heapDigest state base node)
    (parents : HeapParents compress state base leaves m) :
    HeapParents compress next base leaves (m-1) := by
  intro node after below
  rw [preserved (2*node) (by omega) (by omega), preserved (2*node+1) (by omega) (by omega)]
  by_cases current : node = m
  · subst node
    exact written
  · rw [preserved node current (by omega)]
    exact parents node (by omega) below

/-- Pointer registers after one deterministic iteration. -/
theorem parent_next_pointers (state : MachineState) (base remaining : Nat) (a b : BitVec 256)
    (pointers : ParentPointers state base (remaining+1))
    (bound : base + 192*(remaining+1+63) < 2^64) :
    ParentPointers (parentNextState (parentCallState (parentCallState state 0 a) 1 b))
      base remaining := by
  have keep (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
      (parentCallState (parentCallState state 0 a) 1 b).getReg reg = state.getReg reg := by
    rw [parent_call_register _ 1 (by decide) b reg n10 n12,
      parent_call_register _ 0 (by decide) a reg n10 n12]
  have next := parent_next_registers (parentCallState (parentCallState state 0 a) 1 b)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [next.2.2.2 .x9 (by decide) (by decide), keep .x9 (by decide) (by decide)]
    exact pointers.heap
  · rw [next.1, keep .x21 (by decide) (by decide), pointers.left]
    show BitVec.ofNat 64 (base + 192*(remaining+1+63)) - BitVec.ofNat 64 192 = _
    rw [word_sub_literal _ _ (by omega) (by decide)]
    congr 1 <;> omega
  · rw [next.2.1, keep .x22 (by decide) (by decide), pointers.right]
    show BitVec.ofNat 64 (base + 96*(remaining+1+63)) - BitVec.ofNat 64 96 = _
    rw [word_sub_literal _ _ (by omega) (by decide)]
    congr 1 <;> omega
  · rw [next.2.2.2 .x7 (by decide) (by decide), keep .x7 (by decide) (by decide)]
    exact pointers.stop

/-- Addresses of the calls of the deterministic second step. -/
private theorem second_call_addresses (oracle : Oracle) (state : MachineState) :
    parentSource (parentStep oracle state 0) 1 = parentSource state 1 ∧
    parentOutput (parentStep oracle state 0) 1 = parentOutput state 1 :=
  ⟨parent_source_congr _ _ 1 (parent_step_register oracle state 0 (by decide) .x21 (by decide) (by decide)),
   parent_output_congr _ _ 1 (parent_step_register oracle state 0 (by decide) .x21 (by decide) (by decide))
      (parent_step_register oracle state 0 (by decide) .x22 (by decide) (by decide))⟩

/-- The parent loop changes only the slots of nodes `128 .. 2(r+63)+1`. -/
theorem commit_parents_preserves (oracle : Oracle) (state : MachineState)
    (base remaining : Nat) (pointers : ParentPointers state base remaining)
    (bound : base + 192*remaining + 12096 + 192 ≤ MEMORY_BYTES)
    (address count : Nat) (readBound : address + count ≤ 2^64)
    (outside : ∀ node, 128 ≤ node → node ≤ 2*(remaining+63)+1 →
      address + count ≤ base + heapOffset node ∨ base + heapOffset node + 32 ≤ address) :
    readBuffer (checkEvaluation oracle (commitParents state remaining)).1 address count =
      readBuffer state address count := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  induction remaining generalizing state with
  | zero =>
    rw [commit_parents_evaluation_zero]
  | succ remaining ih =>
    rw [commit_parents_evaluation]
    have addresses := parent_addresses state base (remaining+1) pointers bound
    have second := second_call_addresses oracle state
    have next : ParentPointers (parentNextState (parentStep oracle (parentStep oracle state 0) 1))
        base remaining := parent_next_pointers state base remaining (parentAnswer oracle state 0)
      (parentAnswer oracle (parentStep oracle state 0) 1) pointers (by omega)
    dsimp only
    rw [ih _ next (by omega) (fun node low high => outside node low (by omega))]
    change readBuffer (parentStep oracle (parentStep oracle state 0) 1) address count = _
    have out1 : (parentOutput (parentStep oracle state 0) 1).toNat =
        base + heapOffset (2*(remaining+1+63)) := by
      rw [second.2, addresses.2.2.2, heap_offset_even]; omega
    have out0 : (parentOutput state 0).toNat = base + heapOffset (2*(remaining+1+63)+1) := by
      rw [addresses.2.1, heap_offset_odd]; omega
    rw [parent_step_outside oracle _ 1 _ out1 (by rw [heap_offset_even]; omega) address count readBound
        (outside _ (by omega) (by omega)),
      parent_step_outside oracle state 0 _ out0 (by rw [heap_offset_odd]; omega) address count readBound
        (outside _ (by omega) (by omega))]

/-- After the descending loop, every internal node above the cap level (slots >= 128)
agrees with its final children, provided every pair gap read by the loop is zero. -/
theorem commit_parents_consistent (oracle : Oracle) (state : MachineState)
    (base leaves remaining : Nat) (pointers : ParentPointers state base remaining)
    (aligned : base % 8 = 0) (inside : 2*(remaining+63) + 2 ≤ leaves)
    (bounded : base + 96*leaves ≤ MEMORY_BYTES)
    (gaps : ∀ q, 128 ≤ q → q ≤ 2*(remaining+63)+1 → readBuffer state (base + 96*q + 64) 32 = 0)
    (parents : HeapParents oracle.compression state base leaves (2*(remaining+63)+1)) :
    HeapParents oracle.compression
      (checkEvaluation oracle (commitParents state remaining)).1 base leaves 127 := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have nodeBound (node : Nat) (below : node < 2*leaves) : base + heapOffset node + 32 ≤ 2^64 := by
    have := heap_offset_bound node leaves below; omega
  induction remaining generalizing state with
  | zero =>
    rw [commit_parents_evaluation_zero]
    exact parents
  | succ remaining ih =>
    rw [commit_parents_evaluation]
    have addresses := parent_addresses state base (remaining+1) pointers (by omega)
    have second := second_call_addresses oracle state
    have next : ParentPointers (parentNextState (parentStep oracle (parentStep oracle state 0) 1))
        base remaining := parent_next_pointers state base remaining (parentAnswer oracle state 0)
      (parentAnswer oracle (parentStep oracle state 0) 1) pointers (by omega)
    have out0 : (parentOutput state 0).toNat = base + heapOffset (2*(remaining+1+63)+1) := by
      rw [addresses.2.1, heap_offset_odd]; omega
    have src0 : (parentSource state 0).toNat = base + 96*(2*(remaining+1+63)+1) := by
      rw [addresses.1]; omega
    have out1 : (parentOutput (parentStep oracle state 0) 1).toNat =
        base + heapOffset (2*(remaining+1+63)) := by
      rw [second.2, addresses.2.2.2, heap_offset_even]; omega
    have src1 : (parentSource (parentStep oracle state 0) 1).toNat = base + 96*(2*(remaining+1+63)) := by
      rw [second.1, addresses.2.2.1]; omega
    -- the first call (odd parent 2p+1) and the second call (even parent 2p), p = r+64
    have first := heap_parents_extend oracle.compression state (parentStep oracle state 0) base leaves
      (2*(remaining+1+63)+1) (by omega) (by omega)
      (parent_step_node oracle state 0 base _ src0 out0 aligned (gaps _ (by omega) (by omega)))
      (fun node different below => parent_step_other_node oracle state 0 base _ node out0
        (nodeBound _ (by omega)) (nodeBound node below) different)
      parents
    have gap0 (q : Nat) (low : 128 ≤ q) (high : q ≤ 2*(remaining+1+63)+1) :
        readBuffer (parentStep oracle state 0) (base + 96*q + 64) 32 = 0 := by
      rw [parent_step_gap oracle state 0 base _ q out0 (nodeBound _ (by omega)) (by omega)]
      exact gaps q low high
    have secondStep := heap_parents_extend oracle.compression (parentStep oracle state 0)
      (parentStep oracle (parentStep oracle state 0) 1) base leaves
      (2*(remaining+1+63)) (by omega) (by omega)
      (parent_step_node oracle _ 1 base _ src1 out1 aligned (gap0 _ (by omega) (by omega)))
      (fun node different below => parent_step_other_node oracle _ 1 base _ node out1
        (nodeBound _ (by omega)) (nodeBound node below) different)
      (by simpa using first)
    have gap1 (q : Nat) (low : 128 ≤ q) (high : q ≤ 2*(remaining+63)+1) :
        readBuffer (parentNextState (parentStep oracle (parentStep oracle state 0) 1))
          (base + 96*q + 64) 32 = 0 := by
      change readBuffer (parentStep oracle (parentStep oracle state 0) 1) (base + 96*q + 64) 32 = 0
      rw [parent_step_gap oracle _ 1 base _ q out1 (nodeBound _ (by omega)) (by omega)]
      exact gap0 q low (by omega)
    exact ih _ next (by omega) gap1 (by
      have h : 2*(remaining+1+63) - 1 = 2*(remaining+63)+1 := by omega
      rw [h] at secondStep
      exact secondStep)

/-- The loop writes only nodes below `2(r+63)+2`; every higher heap slot, in
particular every leaf, is unchanged. -/
theorem commit_parents_preserves_digest (oracle : Oracle) (state : MachineState)
    (base remaining node : Nat) (pointers : ParentPointers state base remaining)
    (bound : base + 192*remaining + 12096 + 192 ≤ MEMORY_BYTES)
    (after : 2*(remaining+63)+1 < node) (readBound : base + heapOffset node + 32 ≤ 2^64) :
    heapDigest (checkEvaluation oracle (commitParents state remaining)).1 base node =
      heapDigest state base node := by
  unfold heapDigest
  apply commit_parents_preserves oracle state base remaining pointers bound _ 32 readBound
  intro other _ high
  have : heapOffset other + 32 ≤ heapOffset node := by unfold heapOffset; omega
  omega

/-- Starting at the deepest internal pairs needs no assumptions about pre-existing
parent contents, only zero gaps. The actual loop establishes all parent equations. -/
theorem commit_parents_heap (oracle : Oracle) (state : MachineState) (base remaining : Nat)
    (pointers : ParentPointers state base remaining) (aligned : base % 8 = 0)
    (bounded : base + 96*(2*(remaining+63)+2) ≤ MEMORY_BYTES)
    (gaps : ∀ q, 128 ≤ q → q < 2*(remaining+63)+2 → readBuffer state (base + 96*q + 64) 32 = 0) :
    HeapParents oracle.compression
      (checkEvaluation oracle (commitParents state remaining)).1 base (2*(remaining+63)+2) 127 :=
  commit_parents_consistent oracle state base (2*(remaining+63)+2) remaining pointers aligned
    (by omega) bounded (fun q low high => gaps q low (by omega)) (by intro node after below; omega)

end CommitGolfCandidate
