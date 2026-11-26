import CommitGolfCandidate.CommitTree
import CommitGolfCandidate.CheckEvaluation
import CommitGolfCandidate.WriteMemory
import CommitGolfCandidate.HeapModel
import CommitGolfCandidate.HeapLayout

/-! Contents of the actual bottom-up 32-parent commitment gap heap. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

/-- Digest stored at a node of the machine's gap heap, including its unused slot zero. -/
def heapDigest (state : MachineState) (base node : Nat) : Digest :=
  readBuffer state (base + heapOffset node) 32

private theorem memory_read_congr (left right : MachineState) (same : left.mem = right.mem)
    (address count : Nat) : readBuffer left address count = readBuffer right address count := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem, same]

def parentAnswer (oracle : Oracle) (state : MachineState) (u : Nat) : BitVec 256 :=
  oracle.compression (readBuffer state (parentSource state u).toNat 96)

def parentStep (oracle : Oracle) (state : MachineState) (u : Nat) : MachineState :=
  parentCallState state u (parentAnswer oracle state u)

theorem parent_calls_eval_succ (oracle : Oracle) (state : MachineState) (start count : Nat) :
    checkEvaluation oracle (parentCallsRun state start (count + 1)) =
      let rest := checkEvaluation oracle (parentCallsRun (parentStep oracle state (31 - start)) (start + 1) count)
      (rest.1, 1 + rest.2) := by
  rw [parentCallsRun, check_evaluation_public_bind]
  rfl

theorem parent_iteration_evaluation (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (parentIterationRun state)).1 =
      parentNextState (checkEvaluation oracle (parentCallsRun state 0 32)).1 := by
  rw [parentIterationRun, check_evaluation_bind]
  simp only [check_evaluation_pure]

theorem commit_parents_evaluation_zero (oracle : Oracle) (state : MachineState) :
    (checkEvaluation oracle (commitParents state 0)).1 =
      (checkEvaluation oracle (parentCallsRun state 0 31)).1 := rfl

private theorem parent_next_mem (s : MachineState) : (parentNextState s).mem = s.mem := rfl

theorem commit_parents_evaluation (oracle : Oracle) (state : MachineState) (remaining : Nat) :
    (checkEvaluation oracle (commitParents state (remaining + 1))).1 =
      (checkEvaluation oracle (commitParents
        (parentNextState (checkEvaluation oracle (parentCallsRun state 0 32)).1) remaining)).1 := by
  rw [commitParents, check_evaluation_bind]
  have hp := parent_iteration_evaluation oracle state
  rcases h1 : checkEvaluation oracle (parentIterationRun state) with ⟨v, f⟩
  rw [h1] at hp
  dsimp only at hp ⊢
  rw [hp]

theorem parent_step_register (oracle : Oracle) (state : MachineState) (u : Nat)
    (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (parentStep oracle state u).getReg reg = state.getReg reg :=
  parent_call_register state u _ reg n10 n12

theorem parent_step_written (oracle : Oracle) (state : MachineState) (u out : Nat)
    (hout : (parentOutput state u).toNat = out) :
    readBuffer (parentStep oracle state u) out 32 = parentAnswer oracle state u := by
  have outWord : parentOutput state u = BitVec.ofNat 64 out := by
    rw [word_ofNat_toNat (parentOutput state u), hout]
  unfold parentStep
  rw [memory_read_congr _ _ (parent_call_memory state u _), outWord]
  simpa using write_bits_digest state out 0 (parentAnswer oracle state u) (by decide) (by decide)

theorem parent_step_outside (oracle : Oracle) (state : MachineState) (u out : Nat)
    (hout : (parentOutput state u).toNat = out) (outBound : out + 32 ≤ 2^64)
    (address count : Nat) (readBound : address + count ≤ 2^64)
    (separate : address + count ≤ out ∨ out + 32 ≤ address) :
    readBuffer (parentStep oracle state u) address count = readBuffer state address count := by
  have outWord : parentOutput state u = BitVec.ofNat 64 out := by
    rw [word_ofNat_toNat (parentOutput state u), hout]
  unfold parentStep
  rw [memory_read_congr _ _ (parent_call_memory state u _), outWord]
  exact write_bits_read_outside state _ out address count (by simpa using outBound) readBound
    (by simpa using separate)

private theorem pad_pair (right left : BitVec 256) :
    ((0 : BitVec 256) ++ right) ++ left = padInput (right ++ left) := by
  unfold padInput
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append]
  simp

theorem parent_answer_combine (oracle : Oracle) (state : MachineState) (u base q : Nat)
    (hsource : (parentSource state u).toNat = base + 96 * q) (aligned : base % 8 = 0)
    (gap : readBuffer state (base + 96 * q + 64) 32 = 0) :
    parentAnswer oracle state u =
      combine oracle.compression (heapDigest state base (2 * q)) (heapDigest state base (2 * q + 1)) := by
  have alignedMid : (base + 96 * q + 32) % 8 = 0 := by omega
  have h96 : readBuffer state (base + 96 * q) 96 =
      (readBuffer state (base + 96 * q + 32 + 32) 32 ++ readBuffer state (base + 96 * q + 32) 32) ++
        readBuffer state (base + 96 * q) 32 := by
    rw [read_leaf_query state (base + 96 * q), read_compression_halves state (base + 96 * q + 32) alignedMid]
  have e64 : base + 96 * q + 32 + 32 = base + 96 * q + 64 := by omega
  have eOdd : base + heapOffset (2 * q + 1) = base + 96 * q + 32 := by rw [heap_offset_odd]; omega
  have eEven : base + heapOffset (2 * q) = base + 96 * q := by rw [heap_offset_even]
  have input : readBuffer state (parentSource state u).toNat 96 =
      padInput (readBuffer state (base + heapOffset (2 * q + 1)) 32 ++
        readBuffer state (base + heapOffset (2 * q)) 32) := by
    rw [eOdd, eEven, hsource, h96, e64, gap]
    exact pad_pair _ _
  exact congrArg oracle.compression input

theorem parent_step_node (oracle : Oracle) (state : MachineState) (u base q : Nat)
    (hsource : (parentSource state u).toNat = base + 96 * q)
    (hout : (parentOutput state u).toNat = base + heapOffset q) (aligned : base % 8 = 0)
    (gap : readBuffer state (base + 96 * q + 64) 32 = 0) :
    heapDigest (parentStep oracle state u) base q =
      combine oracle.compression (heapDigest state base (2 * q)) (heapDigest state base (2 * q + 1)) := by
  show readBuffer (parentStep oracle state u) (base + heapOffset q) 32 = _
  rw [parent_step_written oracle state u _ hout]
  exact parent_answer_combine oracle state u base q hsource aligned gap

theorem parent_step_other_node (oracle : Oracle) (state : MachineState) (u base m node : Nat)
    (hout : (parentOutput state u).toNat = base + heapOffset m)
    (bound : base + heapOffset m + 32 ≤ 2^64) (readBound : base + heapOffset node + 32 ≤ 2^64)
    (different : node ≠ m) :
    heapDigest (parentStep oracle state u) base node = heapDigest state base node := by
  have disjoint := heap_offset_disjoint node m different
  exact parent_step_outside oracle state u _ hout bound _ 32 readBound (by omega)

theorem parent_step_gap (oracle : Oracle) (state : MachineState) (u base m q : Nat)
    (hout : (parentOutput state u).toNat = base + heapOffset m)
    (bound : base + heapOffset m + 32 ≤ 2^64) (readBound : base + 96 * q + 96 ≤ 2^64) :
    readBuffer (parentStep oracle state u) (base + 96 * q + 64) 32 =
      readBuffer state (base + 96 * q + 64) 32 := by
  have gap := heap_offset_gap m q
  exact parent_step_outside oracle state u _ hout bound _ 32 (by omega) (by omega)

def HeapParents (compress : Compression) (state : MachineState)
    (base leaves remaining : Nat) : Prop :=
  ∀ node, remaining < node → node < leaves →
    heapDigest state base node =
      combine compress (heapDigest state base (2 * node)) (heapDigest state base (2 * node + 1))

theorem heap_parents_extend (compress : Compression) (state next : MachineState)
    (base leaves m : Nat) (positive : 1 ≤ m) (inside : m < leaves)
    (written : heapDigest next base m =
      combine compress (heapDigest state base (2 * m)) (heapDigest state base (2 * m + 1)))
    (preserved : ∀ node, node ≠ m → node < 2 * leaves →
      heapDigest next base node = heapDigest state base node)
    (parents : HeapParents compress state base leaves m) :
    HeapParents compress next base leaves (m - 1) := by
  intro node after below
  rw [preserved (2 * node) (by omega) (by omega), preserved (2 * node + 1) (by omega) (by omega)]
  by_cases current : node = m
  · subst node; exact written
  · rw [preserved node current (by omega)]; exact parents node (by omega) below

/-- Pointer preservation across `parentCallsRun`. -/
theorem parent_calls_pointers (oracle : Oracle) (state : MachineState) (base remaining start count : Nat)
    (pointers : ParentPointers state base remaining) :
    ParentPointers (checkEvaluation oracle (parentCallsRun state start count)).1 base remaining := by
  have keep := (parent_calls_registers state _ start count (check_evaluation_support oracle _)).2
  exact ⟨(keep .x9 (by decide) (by decide)).trans pointers.heap,
    (keep .x21 (by decide) (by decide)).trans pointers.src,
    (keep .x22 (by decide) (by decide)).trans pointers.dst,
    (keep .x24 (by decide) (by decide)).trans pointers.stride⟩

/-- Pointer registers after one deterministic 32-parent iteration. -/
theorem parent_next_pointers (oracle : Oracle) (state : MachineState) (base remaining : Nat)
    (pointers : ParentPointers state base (remaining + 1))
    (bound : base + 3072 * (remaining + 1) + 1536 < 2^64) :
    ParentPointers (parentNextState (checkEvaluation oracle (parentCallsRun state 0 32)).1)
      base remaining := by
  have p := parent_calls_pointers oracle state base (remaining + 1) 0 32 pointers
  have next := parent_next_registers (checkEvaluation oracle (parentCallsRun state 0 32)).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [next.2.2.2 .x9 (by decide) (by decide)]; exact p.heap
  · rw [next.1, p.src, p.stride]
    show BitVec.ofNat 64 (base + 3072 * (remaining + 1) + 1536) - BitVec.ofNat 64 3072 = _
    rw [word_sub_literal _ _ (by clear * -; omega) (by decide)]
    exact congrArg (BitVec.ofNat 64) (by clear * -; omega)
  · rw [next.2.1, p.dst]
    show BitVec.ofNat 64 (base + 1536 * (remaining + 1)) - BitVec.ofNat 64 1536 = _
    rw [word_sub_literal _ _ (by clear * -; omega) (by decide)]
    exact congrArg (BitVec.ofNat 64) (by clear * -; omega)
  · rw [next.2.2.2 .x24 (by decide) (by decide)]; exact p.stride

/-- `parentCallsRun` preserves any range outside the slots of nodes
`32*remaining + (31 - j)` for `start ≤ j < start + count`. -/
theorem parent_calls_preserves (oracle : Oracle) (state : MachineState)
    (base remaining start count : Nat) (bounded : start + count ≤ 32)
    (pointers : ParentPointers state base remaining)
    (bound : base + 3072 * remaining + 3072 ≤ MEMORY_BYTES)
    (address bytes : Nat) (readBound : address + bytes ≤ 2^64)
    (outside : ∀ j, start ≤ j → j < start + count →
      address + bytes ≤ base + heapOffset (32 * remaining + (31 - j)) ∨
      base + heapOffset (32 * remaining + (31 - j)) + 32 ≤ address) :
    readBuffer (checkEvaluation oracle (parentCallsRun state start count)).1 address bytes =
      readBuffer state address bytes := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  induction count generalizing state start with
  | zero => rw [parentCallsRun, check_evaluation_pure]
  | succ count ih =>
    have addr := parent_addresses state base remaining (31 - start) (by omega) pointers bound
    have hOff : heapOffset (32 * remaining + (31 - start)) + 32 ≤ 1536 * remaining + 1536 := by
      unfold heapOffset; omega
    have nextPtr : ParentPointers (parentStep oracle state (31 - start)) base remaining :=
      ⟨(parent_step_register oracle state _ .x9 (by decide) (by decide)).trans pointers.heap,
       (parent_step_register oracle state _ .x21 (by decide) (by decide)).trans pointers.src,
       (parent_step_register oracle state _ .x22 (by decide) (by decide)).trans pointers.dst,
       (parent_step_register oracle state _ .x24 (by decide) (by decide)).trans pointers.stride⟩
    rw [parent_calls_eval_succ]
    dsimp only
    rw [ih _ (start + 1) (by omega) nextPtr (fun j hlo hhi => outside j (by omega) (by omega))]
    exact parent_step_outside oracle state (31 - start) _ addr.2 (by omega) address bytes readBound
      (outside start (by omega) (by omega))

/-- The parent loop and 31-parent tail change only the slots of nodes `1 .. 32*remaining + 31`. -/
theorem commit_parents_preserves (oracle : Oracle) (state : MachineState)
    (base remaining : Nat) (pointers : ParentPointers state base remaining)
    (bound : base + 3072 * remaining + 3072 ≤ MEMORY_BYTES)
    (address bytes : Nat) (readBound : address + bytes ≤ 2^64)
    (outside : ∀ node, 1 ≤ node → node ≤ 32 * remaining + 31 →
      address + bytes ≤ base + heapOffset node ∨ base + heapOffset node + 32 ≤ address) :
    readBuffer (checkEvaluation oracle (commitParents state remaining)).1 address bytes =
      readBuffer state address bytes := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  induction remaining generalizing state with
  | zero =>
    rw [commit_parents_evaluation_zero]
    exact parent_calls_preserves oracle state base 0 0 31 (by decide) pointers bound
      address bytes readBound
      (fun j _ hj => by simpa only [Nat.mul_zero, Nat.zero_add] using outside (31 - j) (by omega) (by omega))
  | succ remaining ih =>
    rw [commit_parents_evaluation]
    have next := parent_next_pointers oracle state base remaining pointers (by omega)
    rw [ih _ next (by omega) (fun node low high => outside node low (by omega))]
    rw [memory_read_congr _ _ (parent_next_mem _)]
    exact parent_calls_preserves oracle state base (remaining + 1) 0 32 (by decide) pointers bound
      address bytes readBound (fun j _ hj => outside (32 * (remaining + 1) + (31 - j)) (by omega) (by omega))

/-- `parentCallsRun` extends `HeapParents` downward by `count` nodes and preserves all pair gaps. -/
theorem parent_calls_consistent (oracle : Oracle) (state : MachineState)
    (base leaves remaining start count : Nat) (bounded : start + count ≤ 32)
    (nonzero : 1 ≤ 32 * remaining + (32 - (start + count)))
    (pointers : ParentPointers state base remaining)
    (aligned : base % 8 = 0) (inside : 32 * remaining + 32 ≤ leaves)
    (memBound : base + 96 * leaves ≤ MEMORY_BYTES)
    (gaps : ∀ q, 1 ≤ q → q ≤ 32 * remaining + (31 - start) → readBuffer state (base + 96 * q + 64) 32 = 0)
    (parents : HeapParents oracle.compression state base leaves (32 * remaining + (31 - start))) :
    HeapParents oracle.compression
      (checkEvaluation oracle (parentCallsRun state start count)).1 base leaves
      (32 * remaining + (31 - start) - count) ∧
    ∀ q, 1 ≤ q → q ≤ 32 * remaining + (31 - start) - count →
      readBuffer (checkEvaluation oracle (parentCallsRun state start count)).1 (base + 96 * q + 64) 32 = 0 := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  have nodeBound (node : Nat) (below : node < 2 * leaves) : base + heapOffset node + 32 ≤ 2^64 := by
    have := heap_offset_bound node leaves below; omega
  induction count generalizing state start with
  | zero =>
    rw [parentCallsRun, check_evaluation_pure]
    simpa only [Nat.sub_zero] using ⟨parents, gaps⟩
  | succ count ih =>
    let u := 31 - start
    let m := 32 * remaining + u
    have addr := parent_addresses state base remaining u (by omega) pointers (by omega)
    have nextPtr : ParentPointers (parentStep oracle state u) base remaining :=
      ⟨(parent_step_register oracle state _ .x9 (by decide) (by decide)).trans pointers.heap,
       (parent_step_register oracle state _ .x21 (by decide) (by decide)).trans pointers.src,
       (parent_step_register oracle state _ .x22 (by decide) (by decide)).trans pointers.dst,
       (parent_step_register oracle state _ .x24 (by decide) (by decide)).trans pointers.stride⟩
    have ext := heap_parents_extend oracle.compression state (parentStep oracle state u) base leaves m
      (by omega) (by omega)
      (parent_step_node oracle state u base m addr.1 addr.2 aligned (gaps m (by omega) (by omega)))
      (fun node diff below => parent_step_other_node oracle state u base m node addr.2
        (nodeBound m (by omega)) (nodeBound node below) diff)
      parents
    have nextGaps (q : Nat) (hlo : 1 ≤ q) (hhi : q ≤ 32 * remaining + (31 - (start + 1))) :
        readBuffer (parentStep oracle state u) (base + 96 * q + 64) 32 = 0 := by
      rw [parent_step_gap oracle state u base m q addr.2 (nodeBound m (by omega)) (by omega)]
      exact gaps q hlo (by omega)
    rw [parent_calls_eval_succ]
    dsimp only
    by_cases hlast : count = 0
    · subst count
      rw [parentCallsRun, check_evaluation_pure]
      refine ⟨ext, fun q hlo hhi => ?_⟩
      rw [parent_step_gap oracle state u base m q addr.2 (nodeBound m (by omega)) (by omega)]
      exact gaps q hlo (by omega)
    · have hm1 : m - 1 = 32 * remaining + (31 - (start + 1)) := by omega
      have hres := ih (parentStep oracle state u) (start + 1) (by omega) (by omega) nextPtr
        nextGaps (by rw [← hm1]; exact ext)
      have hfinal : 32 * remaining + (31 - (start + 1)) - count =
          32 * remaining + (31 - start) - (count + 1) := by omega
      rw [hfinal] at hres
      exact hres

/-- After the descending 32-parent loop and 31-parent tail, every internal node agrees
with its final children, provided every pair gap is zero. -/
theorem commit_parents_consistent (oracle : Oracle) (state : MachineState)
    (base leaves remaining : Nat) (pointers : ParentPointers state base remaining)
    (aligned : base % 8 = 0) (inside : 32 * remaining + 32 ≤ leaves)
    (bounded : base + 96 * leaves ≤ MEMORY_BYTES)
    (gaps : ∀ q, 1 ≤ q → q ≤ 32 * remaining + 31 → readBuffer state (base + 96 * q + 64) 32 = 0)
    (parents : HeapParents oracle.compression state base leaves (32 * remaining + 31)) :
    HeapParents oracle.compression
      (checkEvaluation oracle (commitParents state remaining)).1 base leaves 0 := by
  have mem : MEMORY_BYTES = 2^36 := rfl
  induction remaining generalizing state with
  | zero =>
    rw [commit_parents_evaluation_zero]
    have res := parent_calls_consistent oracle state base leaves 0 0 31 (by decide) (by decide)
      pointers aligned inside bounded gaps parents
    exact res.1
  | succ remaining ih =>
    rw [commit_parents_evaluation]
    have res := parent_calls_consistent oracle state base leaves (remaining + 1) 0 32 (by decide)
      (by omega) pointers aligned inside bounded gaps parents
    have next := parent_next_pointers oracle state base remaining pointers (by omega)
    have hrem : 32 * (remaining + 1) + (31 - 0) - 32 = 32 * remaining + 31 := by omega
    rw [hrem] at res
    have hmem : ∀ a c, readBuffer (parentNextState (checkEvaluation oracle (parentCallsRun state 0 32)).1) a c =
        readBuffer (checkEvaluation oracle (parentCallsRun state 0 32)).1 a c := fun a c =>
      memory_read_congr _ _ rfl a c
    exact ih _ next (by omega)
      (fun q hlo hhi => (hmem _ _).trans (res.2 q hlo hhi))
      (fun node hlo hhi => by simp only [heapDigest, hmem]; exact res.1 node hlo hhi)

/-- The parent phase writes only nodes `1 .. 32*remaining + 31`; every higher node is preserved. -/
theorem commit_parents_preserves_digest (oracle : Oracle) (state : MachineState)
    (base remaining node : Nat) (pointers : ParentPointers state base remaining)
    (bound : base + 3072 * remaining + 3072 ≤ MEMORY_BYTES)
    (after : 32 * remaining + 31 < node) (readBound : base + heapOffset node + 32 ≤ 2^64) :
    heapDigest (checkEvaluation oracle (commitParents state remaining)).1 base node =
      heapDigest state base node := by
  unfold heapDigest
  apply commit_parents_preserves oracle state base remaining pointers bound _ 32 readBound
  intro other _ high
  have : heapOffset other + 32 ≤ heapOffset node := by unfold heapOffset; omega
  omega

/-- Starting at the deepest internal block establishes all parent equations from zero gaps. -/
theorem commit_parents_heap (oracle : Oracle) (state : MachineState) (base remaining : Nat)
    (pointers : ParentPointers state base remaining) (aligned : base % 8 = 0)
    (bounded : base + 96 * (32 * remaining + 32) ≤ MEMORY_BYTES)
    (gaps : ∀ q, 1 ≤ q → q < 32 * remaining + 32 → readBuffer state (base + 96 * q + 64) 32 = 0) :
    HeapParents oracle.compression
      (checkEvaluation oracle (commitParents state remaining)).1 base (32 * remaining + 32) 0 :=
  commit_parents_consistent oracle state base (32 * remaining + 32) remaining pointers aligned
    (by omega) bounded (fun q low high => gaps q low (by omega)) (by intro node after below; omega)

end CommitGolfCandidate
