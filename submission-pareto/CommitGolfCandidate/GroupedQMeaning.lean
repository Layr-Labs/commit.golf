import CommitGolfCandidate.GroupedQLoop
import CommitGolfCandidate.TwoPermutationHeapInvariant
import CommitGolfCandidate.TwoPermutationPackedParentMeaning
import CommitGolfCandidate.TwoPermutationInputWords

/-!
# What the level-21 loop and the heap loop compute

`TailContent s heap before r`: every heap node `r < n < 2^22` holds `heap n`, and every word from
the first group reply upwards is still `before`. The level-21 loop starts from `TailContent _ _ _ (2^22-1)`
(nothing written) and ends at `2^21-1`; the heap loop (levels 20..1) continues down to `0`.
The level-21 inputs are the unit pairs `[s_U, s_U+64)` (`UnitPairs`), which the loops never write.
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate (read_buffer_memory_congr checkEvaluation check_evaluation_bind check_evaluation_pure
  write_bits_read_outside write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
attribute [local irreducible] readBuffer writeBits checkEvaluation

/-- First word the tail must keep: block `B_0` (everything the tail writes lies below, in the heap). -/
def unitFloor : Nat := cellFirst

structure TailContent (s : MachineState) (heap : Nat → BitVec 256) (before : Memory) (remaining : Nat) : Prop where
  nodes : ∀ n, remaining<n → n<4194304 → nodeDigest s n=heap n
  high : ∀ w, unitFloor≤w → w<2^33 → memoryView s w=before w

/-- The level-21 input words of every unit: node `2U+1` above node `2U` (heap leaves `2^22 + g`). -/
def UnitPairs (m : Memory) (heap : Nat → BitVec 256) : Prop :=
  ∀ U < 2097152, ∀ k < 8, m (unitBase U+k) =
    (heap (4194304+(2*U+1)) ++ heap (4194304+2*U)).extractLsb' (64*k) 64

theorem tail_content_setpc (s : MachineState) (pc : Word) (heap : Nat → BitVec 256) (before : Memory)
    (n : Nat) (r : TailContent s heap before n) : TailContent (s.setPC pc) heap before n := by
  refine ⟨?_,r.high⟩
  intro j lo hi
  rw [nodeDigest,read_buffer_memory_congr _ s (show (s.setPC pc).mem=s.mem from rfl)]
  exact r.nodes j lo hi

/-- Writing a node below `2^22` leaves the other nodes and the unit area alone. -/
theorem node_write_frame (s t : MachineState) (heap : Nat → BitVec 256) (before : Memory)
    (cur : Nat) (reply : BitVec 256) (small : cur<4194304) (memory : t.mem=(parentWritten s cur reply).mem)
    (prior : TailContent s heap before cur) (value : reply=heap cur) :
    TailContent t heap before (cur-1) := by
  have writeRange : 8*treeWord cur+32 ≤ 2^64 := by unfold treeWord;omega
  constructor
  · intro j larger lt
    unfold nodeDigest
    rw [read_buffer_memory_congr _ (parentWritten s cur reply) memory]
    by_cases last : j=cur
    · subst j
      have written := write_bits_digest (bits := 256) s (8*treeWord cur) 0 reply (by decide) (by decide)
      simp only [Nat.add_zero,Nat.mul_zero,BitVec.extractLsb'_eq_self] at written
      exact written.trans value
    · have diff : cur<j := by omega
      apply Eq.trans _ (prior.nodes j diff lt)
      apply write_bits_read_outside (bits := 256) s reply (8*treeWord cur) (8*treeWord j) 32 writeRange
      · unfold treeWord;omega
      · right;unfold treeWord;omega
  · intro w lo hi
    rw [←read_word,read_buffer_memory_congr _ (parentWritten s cur reply) memory]
    have sep := write_bits_read_outside (bits:=256) s reply (8*treeWord cur) (8*w) 8 writeRange
      (by omega) (by right; unfold treeWord unitFloor cellFirst at *;omega)
    exact sep.trans ((read_word s w).trans (prior.high w lo hi))

theorem unit_input (s : MachineState) (heap : Nat → BitVec 256) (before : Memory) (r : Nat)
    (prior : TailContent s heap before r) (pairs : UnitPairs before heap) (U : Nat) (hU : U<2097152) :
    l21Input s (U+1) = heap (4194304+(2*U+1)) ++ heap (4194304+2*U) := by
  unfold l21Input
  rw [l21_source_unit]
  apply aligned_buffer_eq _ _ _ (by decide)
  intro k hk
  exact (prior.high _ (by unfold unitBase unitFloor unitFirst; omega) (by unfold unitBase unitFirst cellFirst unitStride; omega)).trans
    (pairs U hU k hk)

theorem l21_content_step (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (before : Memory) (p : Nat) (inside : p<2097152)
    (tree : heap (l21Node (p+1))=oracle.compression (heap (4194304+(2*p+1)) ++ heap (4194304+2*p)))
    (pairs : UnitPairs before heap)
    (prior : TailContent s heap before (l21Node (p+1))) (regs : L21Regs s (p+1)) :
    TailContent (l21After s (p+1) (oracle.compression (l21Input s (p+1)))) heap before (l21Node p) := by
  have input := unit_input s heap before _ prior pairs p inside
  have memory := l21_after_memory s (p+1) (oracle.compression (l21Input s (p+1)))
  have step := node_write_frame s _ heap before (l21Node (p+1)) _ (by unfold l21Node; omega) memory prior
    (by rw [input,tree])
  simpa only [show l21Node (p+1)-1=l21Node p by unfold l21Node; omega] using step

theorem l21_sequence_semantics (oracle : Oracle) (state : MachineState) (heap : Nat → BitVec 256)
    (before : Memory) (remaining count : Nat) (inside : remaining+count ≤ 2097152)
    (tree : ∀ U < 2097152, heap (2097152+U)=oracle.compression (heap (4194304+(2*U+1)) ++ heap (4194304+2*U)))
    (pairs : UnitPairs before heap)
    (prior : TailContent state heap before (l21Node (remaining+count)))
    (regs : L21Regs state (remaining+count)) :
    let result := (checkEvaluation oracle (l21Trace remaining count state)).1
    TailContent result heap before (l21Node remaining) ∧ L21Regs result remaining := by
  induction count generalizing state with
  | zero =>
    simpa only [l21Trace,check_evaluation_pure,Nat.add_zero] using And.intro prior regs
  | succ count ih =>
    rw [l21Trace,check_evaluation_bind]
    have evaluated : checkEvaluation oracle (liftM
        (World.query (.inr (.inl (l21Input state (remaining+(count+1)))))) : OracleComp World (BitVec 256)) =
          (oracle.compression (l21Input state (remaining+(count+1))),1) :=
      CommitGolfCandidate.check_evaluation_public oracle _
    rw [evaluated]
    apply ih _ (by omega)
    · rw [show remaining+(count+1)=(remaining+count)+1 by omega] at prior regs ⊢
      exact l21_content_step oracle state heap before (remaining+count) (by omega)
        (by rw [show l21Node (remaining+count+1)=2097152+(remaining+count) by unfold l21Node; omega]
            exact tree _ (by omega))
        pairs prior regs
    · exact l21_next_regs state (remaining+count) _ (by simpa only [Nat.add_assoc] using regs)

theorem l21_groups_semantics (oracle : Oracle) (base : Word) (span groups : Nat)
    (state : MachineState) (heap : Nat → BitVec 256) (before : Memory)
    (inside : span*groups ≤ 2097152)
    (tree : ∀ U < 2097152, heap (2097152+U)=oracle.compression (heap (4194304+(2*U+1)) ++ heap (4194304+2*U)))
    (pairs : UnitPairs before heap)
    (prior : TailContent state heap before (l21Node (span*groups))) (regs : L21Regs state (span*groups)) :
    TailContent (checkEvaluation oracle (l21Groups base span groups state)).1 heap before (l21Node 0) := by
  induction groups generalizing state with
  | zero => simpa only [l21Groups,check_evaluation_pure,Nat.mul_zero] using prior
  | succ groups ih =>
    rw [Nat.mul_succ] at inside prior regs
    have body := l21_sequence_semantics oracle state heap before (span*groups) span inside tree pairs prior regs
    rw [l21Groups,check_evaluation_bind]
    apply ih _ (by omega)
    · exact tail_content_setpc _ _ _ _ _ body.1
    · exact ⟨body.2.source,body.2.target,body.2.selector,body.2.size,body.2.primitive,body.2.heap,body.2.stop⟩

/-! The heap loop (levels 20..1): the record's packed parents over `TailContent`. -/

theorem heap_content_step (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (before : Memory) (n : Nat) (inside : n+1<2097152)
    (tree : heap (n+1)=projectReply (oracle.compression (heap (2*(n+1)+1) ++ heap (2*(n+1)))))
    (prior : TailContent s heap before (n+1)) (regs : ParentRegs s (n+1)) :
    TailContent (packedParentAfter s (n+1) (oracle.compression (parentInput s (n+1)))) heap before n := by
  have memory := packed_parent_memory s (n+1) (oracle.compression (parentInput s (n+1))) regs (by omega)
  have step := node_write_frame s _ heap before (n+1) _ (by omega) memory prior (by
    rw [child_pair,prior.nodes (2*(n+1)+1) (by omega) (by omega),prior.nodes (2*(n+1)) (by omega) (by omega),tree])
  simpa only [Nat.add_sub_cancel] using step

theorem heap_sequence_semantics (oracle : Oracle) (state : MachineState) (heap : Nat → BitVec 256)
    (before : Memory) (remaining count : Nat) (inside : remaining+count<2097152)
    (tree : ∀ node, 0<node → node<2097152 →
      heap node=projectReply (oracle.compression (heap (2*node+1) ++ heap (2*node))))
    (prior : TailContent state heap before (remaining+count))
    (regs : ParentRegs state (remaining+count)) :
    let result := (checkEvaluation oracle (packedParentsTrace remaining count state)).1
    TailContent result heap before remaining ∧ ParentRegs result remaining := by
  induction count generalizing state with
  | zero =>
    simpa only [packedParentsTrace,check_evaluation_pure,Nat.add_zero] using And.intro prior regs
  | succ count ih =>
    rw [packedParentsTrace,check_evaluation_bind]
    have evaluated : checkEvaluation oracle (liftM
        (World.query (.inr (.inl (parentInput state (remaining+(count+1)))))) : OracleComp World (BitVec 256)) =
          (oracle.compression (parentInput state (remaining+(count+1))),1) :=
      CommitGolfCandidate.check_evaluation_public oracle _
    rw [evaluated]
    apply ih _ (by omega)
    · exact heap_content_step oracle state heap before (remaining+count) (by omega)
        (tree _ (by omega) (by omega)) prior regs
    · exact packed_next_parent_regs state (remaining+count) _ regs

theorem heap_groups_semantics (oracle : Oracle) (base : Word) (span groups : Nat)
    (state : MachineState) (heap : Nat → BitVec 256) (before : Memory)
    (inside : span*groups < 2097152)
    (tree : ∀ node, 0 < node → node < 2097152 →
      heap node=projectReply (oracle.compression (heap (2*node+1) ++ heap (2*node))))
    (prior : TailContent state heap before (span*groups)) (regs : ParentRegs state (span*groups)) :
    TailContent (checkEvaluation oracle (packedParentGroups base span groups state)).1 heap before 0 := by
  induction groups generalizing state with
  | zero => simpa only [packedParentGroups,check_evaluation_pure,Nat.mul_zero] using prior
  | succ groups ih =>
    rw [Nat.mul_succ] at inside prior regs
    have body := heap_sequence_semantics oracle state heap before (span*groups) span inside tree prior regs
    rw [packedParentGroups,check_evaluation_bind]
    apply ih _ (by omega)
    · exact tail_content_setpc _ _ _ _ _ body.1
    · exact ⟨body.2.source,body.2.target,body.2.selector,body.2.size,body.2.primitive,body.2.heap⟩

end TwoPermutationPrototype.Grouped
