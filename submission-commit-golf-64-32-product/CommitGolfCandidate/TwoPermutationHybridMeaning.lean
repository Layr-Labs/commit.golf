import CommitGolfCandidate.R1bParentTraceContent
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (read_buffer_slice read_buffer_memory_congr checkEvaluation check_evaluation_bind
  check_evaluation_pure check_evaluation_public_bind write_bits_read_outside write_bits_digest)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] writeBits checkEvaluation parentsTrace packedParentsTrace packedParentGroups hybridLowerFor hybridUpper hybridParentPhase readBuffer R1bParents.trace parentsTraceP hybridLowerForP

private theorem frameContent (heap : Nat → BitVec 256) (salts : Index → BitVec 128) (a b : MachineState) (n : Nat) (mem : a.mem=b.mem) (initial : ParentContent b heap salts n) :
    ParentContent a heap salts n := by
  constructor
  · intro j lo hi;unfold nodeDigest;rw [read_buffer_memory_congr _ b mem];exact initial.nodes j lo hi
  · intro i;unfold nonceBuffer;rw [read_buffer_memory_congr _ b mem];exact initial.nonces i

private theorem upper_content_at (oracle : Oracle) (mid : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128)
    (masked : ∀ (i : Nat), 0 < i → i ≤ hybridCut → heap i=R1bParents.retained i (oracle.compression (heap (2*i+1) ++ heap (2*i))))
    (prior : ParentContent mid heap salts hybridCut) (regs : ParentRegs mid hybridCut) :
    ParentContent (checkEvaluation oracle (hybridUpper (mid.setPC 4180))).1 heap salts 0 := by
  have preserved : (R1bParents.setup (mid.setPC 4180) 5).mem=mid.mem := rfl
  have shifted : ParentRegs (mid.setPC 4180) hybridCut :=
    ⟨regs.source,regs.target,regs.selector,regs.size,regs.primitive,regs.heap⟩
  unfold hybridUpper
  exact new_trace_content oracle _ heap salts hybridCut le_rfl masked (frameContent heap salts _ mid hybridCut preserved prior)
    (R1bParents.setupReady (mid.setPC 4180) rfl shifted)

/-! ### The paired lowest level: pair inputs from the reply area -/

structure LowerContentP (s : MachineState) (heap : Nat → BitVec 256) (remaining : Nat) : Prop where
  nodes : ∀ n, remaining < n → n < LENGTH → nodeDigest s n = heap n
  inputs : ∀ n, hybridCut < n → n < LENGTH → parentInputP s n = heap (2*n+1) ++ heap (2*n)

private theorem full_node_contentP (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (n : Nat) (inside : n+1<LENGTH) (above : hybridCut < n+1)
    (tree : heap (n+1)=oracle.compression (heap (2*(n+1)+1) ++ heap (2*(n+1))))
    (prior : LowerContentP s heap (n+1)) :
    LowerContentP (parentAfterP s (n+1) (oracle.compression (parentInputP s (n+1)))) heap n := by
  let cur := n+1
  let reply : BitVec 256 := oracle.compression (parentInputP s cur)
  have intBound : n+1<2^24 := inside
  have writeRange : 8*treeWord cur+32 ≤ 2^64 := by dsimp [treeWord,cur];omega
  constructor
  · intro j larger small
    unfold nodeDigest
    rw [read_buffer_memory_congr _ (parentWritten s cur reply)
      (show (parentAfterP s cur reply).mem=(parentWritten s cur reply).mem from rfl)]
    by_cases last : j=cur
    · subst j
      have written := write_bits_digest (bits := 256) s (8*treeWord cur) 0 reply (by decide) (by decide)
      simp only [Nat.add_zero,Nat.mul_zero,BitVec.extractLsb'_eq_self] at written
      apply written.trans
      unfold reply
      rw [prior.inputs cur above inside, show heap cur=_ from tree]
    · have diff : cur<j := by dsimp [cur] at *;omega
      apply Eq.trans _ (prior.nodes j diff small)
      apply write_bits_read_outside (bits := 256) s reply (8*treeWord cur) (8*treeWord j) 32 writeRange
      · change j<2^24 at small;unfold treeWord;omega
      · right;unfold treeWord;omega
  · intro m lo hi
    apply Eq.trans _ (prior.inputs m lo hi)
    change readBuffer (parentAfterP s cur reply) (8 * pairWord m) 64 = readBuffer s (8 * pairWord m) 64
    rw [read_buffer_memory_congr _ (parentWritten s cur reply)
      (show (parentAfterP s cur reply).mem=(parentWritten s cur reply).mem from rfl)]
    apply write_bits_read_outside (bits := 256) s reply (8*treeWord cur) (8*pairWord m) 64 writeRange
    · change m<2^24 at hi;unfold pairWord;omega
    · right;unfold treeWord pairWord;change cur<2^24 at intBound;unfold hybridCut at lo;omega

private theorem full_range_contentP (oracle : Oracle) (state : MachineState) (heap : Nat → BitVec 256)
    (remaining count : Nat) (inside : remaining+count<LENGTH) (lower : hybridCut ≤ remaining)
    (tree : ∀ node, hybridCut<node → node<LENGTH →
      heap node=oracle.compression (heap (2*node+1) ++ heap (2*node)))
    (prior : LowerContentP state heap (remaining+count))
    (regs : ParentRegsP state (remaining+count)) :
    let result := (checkEvaluation oracle (parentsTraceP remaining count state)).1
    LowerContentP result heap remaining ∧ ParentRegsP result remaining := by
  induction count generalizing state with
  | zero =>
    simpa only [parentsTraceP,check_evaluation_pure,Nat.add_zero] using And.intro prior regs
  | succ count ih =>
    rw [parentsTraceP,check_evaluation_bind]
    have evaluated : checkEvaluation oracle (liftM
        (World.query (.inr (.inl (parentInputP state (remaining+(count+1)))))) : OracleComp World (BitVec 256)) =
          (oracle.compression (parentInputP state (remaining+(count+1))),1) :=
      CommitGolfCandidate.check_evaluation_public oracle _
    rw [evaluated]
    apply ih _ (by omega)
    · exact full_node_contentP oracle state heap (remaining+count) (by omega) (by omega)
        (tree _ (by omega) (by omega)) prior
    · exact next_parent_regsP state (remaining+count) _ (by unfold hybridCut at lower; omega) regs

theorem lower_content_setpc (s : MachineState) (pc : Word) (heap : Nat → BitVec 256) (r : Nat)
    (prev : LowerContentP s heap r) : LowerContentP (s.setPC pc) heap r := by
  constructor
  · intro n lo hi
    rw [nodeDigest,read_buffer_memory_congr _ s (show (s.setPC pc).mem=s.mem from rfl)]
    exact prev.nodes n lo hi
  · intro n lo hi
    rw [parentInputP,read_buffer_memory_congr _ s (show (s.setPC pc).mem=s.mem from rfl)]
    exact prev.inputs n lo hi

theorem hybrid_lower_contentP (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (span n : Nat) (bound : hybridCut+span*n<LENGTH)
    (tree : ∀ (i : Nat), hybridCut < i → i < LENGTH → heap i=oracle.compression (heap (2*i+1) ++ heap (2*i)))
    (prior : LowerContentP s heap (hybridCut+span*n)) (regs : ParentRegsP s (hybridCut+span*n)) :
    let out := (checkEvaluation oracle (hybridLowerForP span n s)).1
    LowerContentP out heap hybridCut ∧ ParentRegsP out hybridCut := by
  induction n generalizing s with
  | zero => simpa only [hybridLowerForP,check_evaluation_pure,Nat.mul_zero,Nat.add_zero] using And.intro prior regs
  | succ n ih =>
    have amount : hybridCut+span*(n+1)=hybridCut+span*n+span := by rw [Nat.mul_succ,Nat.add_assoc]
    rw [amount] at prior regs bound
    have step := full_range_contentP oracle s heap (hybridCut+span*n) span bound (by omega) tree prior regs
    rw [hybridLowerForP,check_evaluation_bind]
    apply ih _ (by omega)
    · exact lower_content_setpc _ _ _ _ step.1
    · exact ⟨step.2.source,step.2.target,step.2.selector,step.2.size,step.2.primitive,step.2.heap⟩


/-- Heap values below `LENGTH` as given, the machine's own slots above (so the upper levels' leaf-slot and
nonce obligations hold by definition). -/
def upperHeap (heap : Nat → BitVec 256) (s : MachineState) (n : Nat) : BitVec 256 :=
  if n < LENGTH then heap n else nodeDigest s n

private theorem phase_with_contentP (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (span n : Nat) (endBound : hybridCut+span*n<LENGTH)
    (raw : ∀ (i : Nat), hybridCut < i → i < LENGTH → heap i=oracle.compression (heap (2*i+1) ++ heap (2*i)))
    (masked : ∀ (i : Nat), 0 < i → i ≤ hybridCut → heap i=R1bParents.retained i (oracle.compression (heap (2*i+1) ++ heap (2*i))))
    (prior : LowerContentP s heap (hybridCut+span*n)) (regs : ParentRegsP s (hybridCut+span*n)) :
    ∀ j, 0 < j → j < LENGTH → nodeDigest (checkEvaluation oracle (hybridLowerForP span n (hybridStart s) >>= fun low =>
      hybridUpper (low.setPC 4180))).1 j = heap j := by
  have initial : LowerContentP (hybridStart s) heap (hybridCut+span*n) := by
    constructor
    · intro j lo hi;unfold nodeDigest;rw [read_buffer_memory_congr _ s (show (hybridStart s).mem=s.mem from rfl)]
      exact prior.nodes _ lo hi
    · intro j lo hi;unfold parentInputP;rw [read_buffer_memory_congr _ s (show (hybridStart s).mem=s.mem from rfl)]
      exact prior.inputs _ lo hi
  have lower := hybrid_lower_contentP oracle (hybridStart s) heap span n endBound raw initial (hybrid_start_regsP s _ regs)
  let mid := (checkEvaluation oracle (hybridLowerForP span n (hybridStart s))).1
  let heap' := upperHeap heap mid
  let salts' : Index → BitVec 128 := fun i => nonceBuffer mid i.val
  have content : ParentContent mid heap' salts' hybridCut := by
    constructor
    · intro j lo hi
      unfold heap' upperHeap
      split
      · exact lower.1.nodes j lo (by assumption)
      · rfl
    · intro i; rfl
  have masked' : ∀ (i : Nat), 0 < i → i ≤ hybridCut →
      heap' i=R1bParents.retained i (oracle.compression (heap' (2*i+1) ++ heap' (2*i))) := by
    intro i lo hi
    have a : i < LENGTH := by change i < 2^24; unfold hybridCut at hi; omega
    have b : 2*i+1 < LENGTH := by change 2*i+1 < 2^24; unfold hybridCut at hi; omega
    have c : 2*i < LENGTH := by omega
    simp only [heap', upperHeap, a, b, c, ite_true]
    exact masked i lo hi
  have cutRegs := regs_of_cut mid lower.2
  have up := upper_content_at oracle mid heap' salts' masked' content cutRegs
  have whole := content_bound oracle (hybridLowerForP span n (hybridStart s))
    (fun low => hybridUpper (low.setPC 4180)) heap' salts' 0 up
  intro j lo hi
  have value := whole.nodes j lo (by change j < 2^24 at hi; change j < 2*2^24; omega)
  simpa only [heap', upperHeap, hi, ite_true] using value

/-- The paired parent phase computes every internal node of the tree whose leaf level is given by the
reply-area pair inputs. -/
theorem hybrid_parent_content (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 256)
    (raw : ∀ (i : Nat), hybridCut < i → i < LENGTH → heap i=oracle.compression (heap (2*i+1) ++ heap (2*i)))
    (masked : ∀ (i : Nat), 0 < i → i ≤ hybridCut → heap i=R1bParents.retained i (oracle.compression (heap (2*i+1) ++ heap (2*i))))
    (inputs : ∀ n, hybridCut < n → n < LENGTH → parentInputP s n = heap (2*n+1) ++ heap (2*n))
    (regs : ParentRegsP s (2^24-1)) :
    ∀ j, 0 < j → j < LENGTH → nodeDigest (checkEvaluation oracle (hybridParentPhase s)).1 j = heap j := by
  unfold hybridParentPhase hybridLowerP
  have prior : LowerContentP s heap (hybridCut+fullSpan*256) :=
    ⟨fun n lo hi => by change hybridCut+fullSpan*256 < n at lo; change n < 2^24 at hi; unfold hybridCut fullSpan at lo; omega,
      inputs⟩
  have regs' : ParentRegsP s (hybridCut+fullSpan*256) := by
    rw [show hybridCut+fullSpan*256 = 2^24-1 by decide]; exact regs
  exact phase_with_contentP oracle s heap fullSpan 256 (by decide) raw masked prior regs'

private theorem counted_upper (oracle : Oracle) (n : Nat) (s : MachineState) : RunPublic oracle (R1bParents.trace n s) n := by
  induction n generalizing s with
  | zero => rw [R1bParents.trace];exact run_pure_public _ _
  | succ n ih =>
    rw [R1bParents.trace,show n+1=1+n by omega]
    apply run_bind_public _ _ _ 1 n (run_query_public ..)
    intro v;exact ih _

theorem counted_hybrid_phase (oracle : Oracle) (state : MachineState) :
    RunPublic oracle (hybridParentPhase state) 16777215 := by
  unfold hybridParentPhase
  apply run_bind_public _ _ _ 8388608 8388607 (counted_lowerP oracle _ 256)
  intro out
  unfold hybridUpper
  exact counted_upper oracle _ _

end TwoPermutationPrototype.RV64
