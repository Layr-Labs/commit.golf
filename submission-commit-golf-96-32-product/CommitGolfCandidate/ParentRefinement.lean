import CommitGolfCandidate.CommitTree
import CommitGolfCandidate.CheckEvaluation
import CommitGolfCandidate.WriteMemory
import CommitGolfCandidate.HeapModel
import CommitGolfCandidate.HeapLayout

/-! Contents of the actual bottom-up commitment gap heap. Node `s` lives at
`base + heapOffset s`; each parent call reads the contiguous pair `[2q | 2q+1 | gap]`
and, as long as the gap is zero, its input is exactly the reference padded pair. Every
call changes exactly one node slot and never a gap. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 20000

/-- Digest stored at a node of the machine's gap heap, including its unused slot zero. -/
def heapDigest (state : MachineState) (base node : Nat) : Digest :=
  readBuffer state (base + heapOffset node) 32

private theorem memory_read_congr (left right : MachineState) (same : left.mem = right.mem)
    (address count : Nat) : readBuffer left address count = readBuffer right address count := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem, same]

/-- Reply of parent call `j` under a fixed oracle. -/
def parentAnswer (oracle : Oracle) (state : MachineState) (isTail : Bool) (j : Nat) : BitVec 256 :=
  oracle.compression (readBuffer state (parentSource state isTail j).toNat 96)

/-- Parent call `j` evaluated with a fixed oracle. -/
def parentStep (oracle : Oracle) (state : MachineState) (isTail : Bool) (j : Nat) : MachineState :=
  parentCallState state isTail j (parentAnswer oracle state isTail j)

theorem parent_calls_from_evaluation_zero (oracle : Oracle) (state : MachineState)
    (isTail : Bool) (start : Nat) :
    checkEvaluation oracle (parentCallsFrom state isTail start 0) = (state, 0) := by
  rw [parentCallsFrom, check_evaluation_pure]

theorem parent_calls_from_evaluation_succ (oracle : Oracle) (state : MachineState)
    (isTail : Bool) (start count : Nat) :
    checkEvaluation oracle (parentCallsFrom state isTail start (count + 1)) =
      let rest := checkEvaluation oracle
        (parentCallsFrom (parentStep oracle state isTail start) isTail (start + 1) count)
      (rest.1, 1 + rest.2) := by
  rw [parentCallsFrom, check_evaluation_public_bind]
  rfl

theorem parent_iteration_evaluation (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (parentIterationRun state) =
      let hashed := checkEvaluation oracle (parentCallsFrom state false 0 16)
      (parentNextState hashed.1, hashed.2) := by
  rw [parentIterationRun, check_evaluation_bind]
  generalize checkEvaluation oracle (parentCallsFrom state false 0 16) = res
  rcases res with ⟨hashed, calls⟩
  simp only [check_evaluation_pure, Nat.add_zero]

theorem commit_parents_evaluation_zero (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (commitParents state 0) =
      checkEvaluation oracle (parentCallsFrom state true 0 15) := by
  rfl

theorem commit_parents_evaluation (oracle : Oracle) (state : MachineState) (remaining : Nat) :
    checkEvaluation oracle (commitParents state (remaining + 1)) =
      let iter := checkEvaluation oracle (parentIterationRun state)
      let result := checkEvaluation oracle (commitParents iter.1 remaining)
      (result.1, iter.2 + result.2) := by
  rw [commitParents, check_evaluation_bind]

theorem parent_step_register (oracle : Oracle) (state : MachineState) (isTail : Bool) (j : Nat)
    (reg : Reg) (n10 : reg ≠ .x10) (n12 : reg ≠ .x12) :
    (parentStep oracle state isTail j).getReg reg = state.getReg reg :=
  parent_call_register state isTail j _ reg n10 n12

theorem parent_step_written (oracle : Oracle) (state : MachineState) (isTail : Bool) (j out : Nat)
    (hout : (parentOutput state isTail j).toNat = out) :
    readBuffer (parentStep oracle state isTail j) out 32 = parentAnswer oracle state isTail j := by
  have outWord : parentOutput state isTail j = BitVec.ofNat 64 out := by
    rw [word_ofNat_toNat (parentOutput state isTail j), hout]
  unfold parentStep
  rw [memory_read_congr _ _ (parent_call_memory state isTail j _), outWord]
  have written := write_bits_digest state out 0 (parentAnswer oracle state isTail j) (by decide) (by decide)
  simpa using written

theorem parent_step_outside (oracle : Oracle) (state : MachineState) (isTail : Bool) (j out : Nat)
    (hout : (parentOutput state isTail j).toNat = out) (outBound : out + 32 ≤ 2 ^ 64)
    (address count : Nat) (readBound : address + count ≤ 2 ^ 64)
    (separate : address + count ≤ out ∨ out + 32 ≤ address) :
    readBuffer (parentStep oracle state isTail j) address count = readBuffer state address count := by
  have outWord : parentOutput state isTail j = BitVec.ofNat 64 out := by
    rw [word_ofNat_toNat (parentOutput state isTail j), hout]
  unfold parentStep
  rw [memory_read_congr _ _ (parent_call_memory state isTail j _), outWord]
  exact write_bits_read_outside state _ out address count (by simpa using outBound) readBound
    (by simpa using separate)

private theorem pad_pair (right left : BitVec 256) :
    ((0 : BitVec 256) ++ right) ++ left = padInput (right ++ left) := by
  unfold padInput
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append, BitVec.toNat_append]
  simp

/-- The 96-byte pair `[left | right | zero gap]` is the reference padded pair. -/
theorem parent_answer_combine (oracle : Oracle) (state : MachineState) (isTail : Bool)
    (j base q : Nat)
    (hsource : (parentSource state isTail j).toNat = base + 96 * q) (aligned : base % 8 = 0)
    (gap : readBuffer state (base + 96 * q + 64) 32 = 0) :
    parentAnswer oracle state isTail j =
      combine oracle.compression (heapDigest state base (2 * q)) (heapDigest state base (2 * q + 1)) := by
  have alignedMid : (base + 96 * q + 32) % 8 = 0 := by omega
  have h96 : readBuffer state (base + 96 * q) 96 =
      (readBuffer state (base + 96 * q + 32 + 32) 32 ++ readBuffer state (base + 96 * q + 32) 32) ++
        readBuffer state (base + 96 * q) 32 := by
    rw [read_leaf_query state (base + 96 * q), read_compression_halves state (base + 96 * q + 32) alignedMid]
  have e64 : base + 96 * q + 32 + 32 = base + 96 * q + 64 := by omega
  have eOdd : base + heapOffset (2 * q + 1) = base + 96 * q + 32 := by rw [heap_offset_odd]; omega
  have eEven : base + heapOffset (2 * q) = base + 96 * q := by rw [heap_offset_even]
  have input : readBuffer state (parentSource state isTail j).toNat 96 =
      padInput (readBuffer state (base + heapOffset (2 * q + 1)) 32 ++
        readBuffer state (base + heapOffset (2 * q)) 32) := by
    rw [eOdd, eEven, hsource, h96, e64, gap]
    exact pad_pair _ _
  exact congrArg oracle.compression input

theorem parent_step_node (oracle : Oracle) (state : MachineState) (isTail : Bool) (j base q : Nat)
    (hsource : (parentSource state isTail j).toNat = base + 96 * q)
    (hout : (parentOutput state isTail j).toNat = base + heapOffset q) (aligned : base % 8 = 0)
    (gap : readBuffer state (base + 96 * q + 64) 32 = 0) :
    heapDigest (parentStep oracle state isTail j) base q =
      combine oracle.compression (heapDigest state base (2 * q)) (heapDigest state base (2 * q + 1)) := by
  show readBuffer (parentStep oracle state isTail j) (base + heapOffset q) 32 = _
  rw [parent_step_written oracle state isTail j _ hout]
  exact parent_answer_combine oracle state isTail j base q hsource aligned gap

theorem parent_step_other_node (oracle : Oracle) (state : MachineState) (isTail : Bool)
    (j base m node : Nat)
    (hout : (parentOutput state isTail j).toNat = base + heapOffset m)
    (bound : base + heapOffset m + 32 ≤ 2 ^ 64) (readBound : base + heapOffset node + 32 ≤ 2 ^ 64)
    (different : node ≠ m) :
    heapDigest (parentStep oracle state isTail j) base node = heapDigest state base node := by
  have disjoint := heap_offset_disjoint node m different
  exact parent_step_outside oracle state isTail j _ hout bound _ 32 readBound (by omega)

theorem parent_step_gap (oracle : Oracle) (state : MachineState) (isTail : Bool)
    (j base m q : Nat)
    (hout : (parentOutput state isTail j).toNat = base + heapOffset m)
    (bound : base + heapOffset m + 32 ≤ 2 ^ 64) (readBound : base + 96 * q + 96 ≤ 2 ^ 64) :
    readBuffer (parentStep oracle state isTail j) (base + 96 * q + 64) 32 =
      readBuffer state (base + 96 * q + 64) 32 := by
  have gap := heap_offset_gap m q
  exact parent_step_outside oracle state isTail j _ hout bound _ 32 (by omega) (by omega)

/-- The suffix of internal nodes already constructed by the descending loop. -/
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
  · subst node
    exact written
  · rw [preserved node current (by omega)]
    exact parents node (by omega) below

/-- Pointer registers after one evaluated 16-parent iteration. -/
theorem parent_next_pointers (oracle : Oracle) (state : MachineState) (base remaining : Nat)
    (pointers : ParentPointers state base (remaining + 1))
    (bound : base + 1536 * (remaining + 1) < 2 ^ 64) :
    ParentPointers (checkEvaluation oracle (parentIterationRun state)).1 base remaining := by
  have regs := parent_iteration_registers state _
    (check_evaluation_support oracle (parentIterationRun state))
  refine ⟨?_, ?_, ?_⟩
  · exact (regs.2.2.2 .x9 (by decide) (by decide) (by decide) (by decide)).trans pointers.heap
  · rw [regs.1, pointers.left]
    show BitVec.ofNat 64 (base + 1536 * (remaining + 1)) - BitVec.ofNat 64 1536 = _
    have hmul : base + 1536 * (remaining + 1) = base + 1536 * remaining + 1536 := by
      rw [Nat.mul_succ, Nat.add_assoc]
    rw [hmul, word_sub_literal _ _ (Nat.le_add_left 1536 _) (by decide), Nat.add_sub_cancel]
  · rw [regs.2.1, pointers.right]
    show BitVec.ofNat 64 (base + 768 * (remaining + 1)) - BitVec.ofNat 64 768 = _
    have hmul : base + 768 * (remaining + 1) = base + 768 * remaining + 768 := by
      rw [Nat.mul_succ, Nat.add_assoc]
    rw [hmul, word_sub_literal _ _ (Nat.le_add_left 768 _) (by decide), Nat.add_sub_cancel]

private theorem heap_offset_block16 (r q : Nat) :
    heapOffset (16 * r + q) = 768 * r + heapOffset q := by
  unfold heapOffset; omega

private theorem parent_step_pointers (oracle : Oracle) (state : MachineState)
    (base r : Nat) (isTail : Bool) (j : Nat) (pointers : ParentPointers state base r) :
    ParentPointers (parentStep oracle state isTail j) base r :=
  ⟨(parent_step_register oracle state isTail j .x9 (by decide) (by decide)).trans pointers.heap,
   (parent_step_register oracle state isTail j .x21 (by decide) (by decide)).trans pointers.left,
   (parent_step_register oracle state isTail j .x22 (by decide) (by decide)).trans pointers.right⟩

/-- Consecutive parent calls only write their corresponding node slots. -/
theorem parent_calls_from_preserves (oracle : Oracle) (state : MachineState)
    (base r : Nat) (isTail : Bool) (start count : Nat)
    (hbound : start + count ≤ if isTail then 15 else 16)
    (pointers : ParentPointers state base r)
    (bound : base + 1536 * r + 1536 ≤ MEMORY_BYTES)
    (address bytes : Nat) (readBound : address + bytes ≤ 2 ^ 64)
    (outside : ∀ k, start ≤ k → k < start + count →
      let node := (if isTail then 0 else 16 * r) + (15 - k)
      address + bytes ≤ base + heapOffset node ∨ base + heapOffset node + 32 ≤ address) :
    readBuffer (checkEvaluation oracle (parentCallsFrom state isTail start count)).1 address bytes =
      readBuffer state address bytes := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  induction count generalizing state start with
  | zero => rw [parent_calls_from_evaluation_zero]
  | succ count ih =>
    have hstart16 : start < 16 := by cases isTail <;> simp at hbound <;> omega
    rw [parent_calls_from_evaluation_succ]
    dsimp only
    rw [ih (parentStep oracle state isTail start) (start + 1) (by omega)
      (parent_step_pointers oracle state base r isTail start pointers)
      (fun k hk1 hk2 => outside k (by omega) (by omega))]
    have addr := parent_addresses state base r pointers bound isTail start hstart16
    let node := (if isTail then 0 else 16 * r) + (15 - start)
    have hout : (parentOutput state isTail start).toNat = base + heapOffset node := by
      rw [addr.2]
      cases isTail
      · simp only [node, Bool.false_eq_true, ↓reduceIte, heap_offset_block16]; omega
      · simp only [node, ↓reduceIte, Nat.zero_add, Nat.add_zero]
    have hnodeBound : base + heapOffset node + 32 ≤ 2 ^ 64 := by
      have hkOff : heapOffset (15 - start) + 32 ≤ 768 := by unfold heapOffset; omega
      cases isTail
      · simp only [node, Bool.false_eq_true, ↓reduceIte, heap_offset_block16]; omega
      · simp only [node, ↓reduceIte, Nat.zero_add]; omega
    exact parent_step_outside oracle state isTail start (base + heapOffset node) hout hnodeBound
      address bytes readBound (outside start (by omega) (by omega))

/-- Consecutive descending parent calls extend `HeapParents` across their entire block. -/
theorem parent_calls_from_consistent (oracle : Oracle) (state : MachineState)
    (base leaves r : Nat) (isTail : Bool) (start count : Nat)
    (hbound : start + count ≤ if isTail then 15 else 16)
    (hpos : isTail = false → 1 ≤ r)
    (pointers : ParentPointers state base r)
    (aligned : base % 8 = 0)
    (inside : (if isTail then 0 else 16 * r) + 16 ≤ leaves)
    (bounded : base + 96 * leaves ≤ MEMORY_BYTES)
    (gaps : ∀ q, 1 ≤ q → q ≤ (if isTail then 0 else 16 * r) + (16 - start) - 1 →
      readBuffer state (base + 96 * q + 64) 32 = 0)
    (parents : HeapParents oracle.compression state base leaves
      ((if isTail then 0 else 16 * r) + (16 - start) - 1)) :
    HeapParents oracle.compression
      (checkEvaluation oracle (parentCallsFrom state isTail start count)).1 base leaves
      ((if isTail then 0 else 16 * r) + (16 - (start + count)) - 1) ∧
    (∀ q, 1 ≤ q → q ≤ (if isTail then 0 else 16 * r) + (16 - (start + count)) - 1 →
      readBuffer (checkEvaluation oracle (parentCallsFrom state isTail start count)).1
        (base + 96 * q + 64) 32 = 0) := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  have nodeBound (node : Nat) (below : node < 2 * leaves) : base + heapOffset node + 32 ≤ 2 ^ 64 := by
    have := heap_offset_bound node leaves below; omega
  induction count generalizing state start with
  | zero =>
    rw [parent_calls_from_evaluation_zero]
    exact ⟨parents, gaps⟩
  | succ count ih =>
    have hstart16 : start < 16 := by cases isTail <;> simp at hbound <;> omega
    let node := (if isTail then 0 else 16 * r) + (15 - start)
    have hmEq : node = (if isTail then 0 else 16 * r) + (16 - start) - 1 := by
      dsimp only [node]
      cases isTail <;> simp only [Bool.false_eq_true, ↓reduceIte] at hbound ⊢ <;> omega
    have hmPos : 1 ≤ node := by
      dsimp only [node]
      cases isTail
      · have := hpos rfl; simp only [Bool.false_eq_true, ↓reduceIte]; omega
      · simp only [↓reduceIte] at hbound ⊢; omega
    have hmLt : node < leaves := by
      dsimp only [node]
      cases isTail <;> simp only [Bool.false_eq_true, ↓reduceIte] at inside hbound ⊢ <;> omega
    have hmPred : node - 1 = (if isTail then 0 else 16 * r) + (16 - (start + 1)) - 1 := by
      dsimp only [node]
      cases isTail
      · have := hpos rfl; simp only [Bool.false_eq_true, ↓reduceIte]; omega
      · simp only [↓reduceIte] at hbound ⊢; omega
    have hsrc : (parentSource state isTail start).toNat = base + 96 * node := by
      dsimp only [node]
      cases isTail
      · simp only [Bool.false_eq_true, ↓reduceIte] at inside ⊢
        have addr := parent_addresses state base r pointers (by omega) false start hstart16
        simp only [Bool.false_eq_true, ↓reduceIte] at addr
        rw [addr.1]; omega
      · simp only [↓reduceIte, Nat.zero_add] at inside ⊢
        show (state.getReg .x9 + BitVec.ofNat 64 (96 * (15 - start))).toNat = _
        rw [pointers.heap, pointer_offset_nat base (96 * (15 - start)) (by omega)]
    have hout : (parentOutput state isTail start).toNat = base + heapOffset node := by
      dsimp only [node]
      cases isTail
      · simp only [Bool.false_eq_true, ↓reduceIte] at inside ⊢
        have addr := parent_addresses state base r pointers (by omega) false start hstart16
        simp only [Bool.false_eq_true, ↓reduceIte] at addr
        rw [addr.2, heap_offset_block16]; omega
      · simp only [↓reduceIte, Nat.zero_add] at inside ⊢
        show (state.getReg .x9 + BitVec.ofNat 64 (heapOffset (15 - start))).toNat = _
        have hkOff : heapOffset (15 - start) + 32 ≤ 768 := by unfold heapOffset; omega
        rw [pointers.heap, pointer_offset_nat base (heapOffset (15 - start)) (by omega)]
    have stepParents : HeapParents oracle.compression (parentStep oracle state isTail start)
        base leaves (node - 1) :=
      heap_parents_extend oracle.compression state (parentStep oracle state isTail start)
        base leaves node hmPos hmLt
        (parent_step_node oracle state isTail start base node hsrc hout aligned
          (gaps node hmPos (Nat.le_of_eq hmEq)))
        (fun other different below => parent_step_other_node oracle state isTail start base node
          other hout (nodeBound node (by omega)) (nodeBound other below) different)
        (by rw [hmEq]; exact parents)
    have stepGaps : ∀ q, 1 ≤ q → q ≤ (if isTail then 0 else 16 * r) + (16 - (start + 1)) - 1 →
        readBuffer (parentStep oracle state isTail start) (base + 96 * q + 64) 32 = 0 := by
      intro q hq1 hq2
      rw [parent_step_gap oracle state isTail start base node q hout (nodeBound node (by omega))
        (by
          have : q < leaves := by cases isTail <;> simp at inside hbound hq2 ⊢ <;> omega
          omega)]
      exact gaps q hq1 (by omega)
    rw [parent_calls_from_evaluation_succ]
    dsimp only
    have res := ih (parentStep oracle state isTail start) (start + 1) (by omega)
      (parent_step_pointers oracle state base r isTail start pointers) stepGaps
      (by rw [← hmPred]; exact stepParents)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using res

attribute [local irreducible] checkEvaluation parentCallsFrom parentIterationRun

private theorem parent_next_mem (s : MachineState) : (parentNextState s).mem = s.mem := by
  cases s; rfl

/-- The parent loop and root tail change only the slots of nodes `1 .. 16*remaining + 15`. -/
theorem commit_parents_preserves (oracle : Oracle) (state : MachineState)
    (base remaining : Nat) (pointers : ParentPointers state base remaining)
    (bound : base + 1536 * remaining + 1536 ≤ MEMORY_BYTES)
    (address count : Nat) (readBound : address + count ≤ 2 ^ 64)
    (outside : ∀ node, 1 ≤ node → node ≤ 16 * remaining + 15 →
      address + count ≤ base + heapOffset node ∨ base + heapOffset node + 32 ≤ address) :
    readBuffer (checkEvaluation oracle (commitParents state remaining)).1 address count =
      readBuffer state address count := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  induction remaining generalizing state with
  | zero =>
    rw [commit_parents_evaluation_zero]
    exact parent_calls_from_preserves oracle state base 0 true 0 15 (by decide) pointers bound
      address count readBound (fun k _ hk => by
        dsimp only; simp only [↓reduceIte, Nat.zero_add]
        exact outside (15 - k) (by omega) (by omega))
  | succ remaining ih =>
    rw [commit_parents_evaluation]
    dsimp only
    have next := parent_next_pointers oracle state base remaining pointers (by omega)
    rw [ih _ next (by omega) (fun node low high => outside node low (by omega))]
    rw [parent_iteration_evaluation, memory_read_congr _ _ (parent_next_mem _)]
    exact parent_calls_from_preserves oracle state base (remaining + 1) false 0 16 (by decide)
      pointers bound address count readBound (fun k _ hk => by
        dsimp only; simp only [Bool.false_eq_true, ↓reduceIte]
        exact outside (16 * (remaining + 1) + (15 - k)) (by omega) (by omega))

/-- After the descending loop and root tail, every internal node agrees with its final
children, provided every pair gap read by the loop is zero. -/
theorem commit_parents_consistent (oracle : Oracle) (state : MachineState)
    (base leaves remaining : Nat) (pointers : ParentPointers state base remaining)
    (aligned : base % 8 = 0) (inside : 16 * remaining + 16 ≤ leaves)
    (bounded : base + 96 * leaves ≤ MEMORY_BYTES)
    (gaps : ∀ q, 1 ≤ q → q ≤ 16 * remaining + 15 → readBuffer state (base + 96 * q + 64) 32 = 0)
    (parents : HeapParents oracle.compression state base leaves (16 * remaining + 15)) :
    HeapParents oracle.compression
      (checkEvaluation oracle (commitParents state remaining)).1 base leaves 0 := by
  have mem : MEMORY_BYTES = 2 ^ 36 := rfl
  induction remaining generalizing state with
  | zero =>
    rw [commit_parents_evaluation_zero]
    have res := parent_calls_from_consistent oracle state base leaves 0 true 0 15 (by decide)
      (by intro h; cases h) pointers aligned (by simp; omega) bounded
      (by intro q hq1 hq2; exact gaps q hq1 (by simpa using hq2))
      (by simpa using parents)
    simpa using res.1
  | succ remaining ih =>
    rw [commit_parents_evaluation]
    dsimp only
    have next := parent_next_pointers oracle state base remaining pointers (by omega)
    have block := parent_calls_from_consistent oracle state base leaves (remaining + 1) false 0 16
      (by decide) (fun _ => by omega) pointers aligned (by simp; omega) bounded
      (by intro q hq1 hq2; simp only [Bool.false_eq_true, ↓reduceIte] at hq2; exact gaps q hq1 (by omega))
      (by rw [show (if false then 0 else 16 * (remaining + 1)) + (16 - 0) - 1 =
            16 * (remaining + 1) + 15 by simp only [Bool.false_eq_true, ↓reduceIte]; omega]; exact parents)
    have hmem : (checkEvaluation oracle (parentIterationRun state)).1.mem =
        (checkEvaluation oracle (parentCallsFrom state false 0 16)).1.mem := by
      rw [parent_iteration_evaluation]; exact parent_next_mem _
    have nextGaps : ∀ q, 1 ≤ q → q ≤ 16 * remaining + 15 →
        readBuffer (checkEvaluation oracle (parentIterationRun state)).1 (base + 96 * q + 64) 32 = 0 := by
      intro q hq1 hq2
      rw [memory_read_congr _ _ hmem]
      exact block.2 q hq1 (by simp; omega)
    have nextParents : HeapParents oracle.compression
        (checkEvaluation oracle (parentIterationRun state)).1 base leaves (16 * remaining + 15) := by
      intro node hn1 hn2
      unfold heapDigest
      rw [memory_read_congr _ _ hmem, memory_read_congr _ _ hmem, memory_read_congr _ _ hmem]
      exact block.1 node (by simp; omega) hn2
    exact ih _ next (by omega) nextGaps nextParents

/-- The loop and root tail write only nodes below `16*remaining + 16`; every higher heap slot,
in particular every leaf, is unchanged. -/
theorem commit_parents_preserves_digest (oracle : Oracle) (state : MachineState)
    (base remaining node : Nat) (pointers : ParentPointers state base remaining)
    (bound : base + 1536 * remaining + 1536 ≤ MEMORY_BYTES)
    (after : 16 * remaining + 15 < node) (readBound : base + heapOffset node + 32 ≤ 2 ^ 64) :
    heapDigest (checkEvaluation oracle (commitParents state remaining)).1 base node =
      heapDigest state base node := by
  unfold heapDigest
  apply commit_parents_preserves oracle state base remaining pointers bound _ 32 readBound
  intro other _ high
  have : heapOffset other + 32 ≤ heapOffset node := by unfold heapOffset; omega
  omega

/-- Starting at the deepest internal nodes needs no assumptions about pre-existing
parent contents, only zero gaps. The actual loop establishes all parent equations. -/
theorem commit_parents_heap (oracle : Oracle) (state : MachineState) (base remaining : Nat)
    (pointers : ParentPointers state base remaining) (aligned : base % 8 = 0)
    (bounded : base + 96 * (16 * remaining + 16) ≤ MEMORY_BYTES)
    (gaps : ∀ q, 1 ≤ q → q < 16 * remaining + 16 → readBuffer state (base + 96 * q + 64) 32 = 0) :
    HeapParents oracle.compression
      (checkEvaluation oracle (commitParents state remaining)).1 base (16 * remaining + 16) 0 :=
  commit_parents_consistent oracle state base (16 * remaining + 16) remaining pointers aligned
    (by omega) bounded (fun q low high => gaps q low (by omega)) (by intro node after below; omega)

end CommitGolfCandidate
