import CommitGolfCandidate.ChainedHeapWords

/-! Fixed-oracle meaning and heap-content preservation of a complete native node. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] nodeTrace checkEvaluation readBuffer

noncomputable def parentDigestTrace (h : Height) (left right : BitVec 238) : OracleComp World Output := do
  let answer ← (liftM (World.query (.inr (.inl (canonicalEncoding.first h (right ++ left))))) : OracleComp World Output)
  let value ← continuationTrace h 0 (calls h-1) answer
  return finalValue h value

noncomputable def parentValue (oracle : Oracle) (h : Height) (left right : BitVec 238) : Output :=
  (checkEvaluation oracle (parentDigestTrace h left right)).1

structure HeapNodeReady (s : MachineState) (h : Height) (node : Nat) : Prop where
  args : LoopArgs s 256
  source : s.getReg .x6 = heapAddress (2*node)
  target : s.getReg .x7 = heapAddress node
  height : s.getReg .x17 = BitVec.ofNat 64 h.val
  mask : s.getReg .x16 = finalMask h
  small : node < 2^24

theorem node_evaluation_value (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 238)
    (h : Height) (node : Nat) (positive : 0 < node) (ready : HeapNodeReady s h node)
    (prior : HeapContent s heap node) :
    heapDigest (checkEvaluation oracle (nodeTrace h s)).1 node =
      parentValue oracle h (heap (2*node)) (heap (2*node+1)) := by
  have inputs := heap_child_words s heap node positive ready.small prior
  rw [←ready.source] at inputs
  have aligned : (s.getReg .x7).toNat % 8 = 0 := by
    rw [ready.target,heap_address_numeric node (by have := ready.small; omega)]
    unfold heapBase
    omega
  have separate : ∀ a b : Fin 4, (256 : Word)+BitVec.ofNat 64 (8*a.val) ≠
      s.getReg .x7+BitVec.ofNat 64 (8*b.val) := by
    intro a b
    rw [ready.target]
    exact Ne.symm (scratch_address_ne _
      (heap_word_outside node b.val (by have := ready.small; omega) (by have := b.isLt; omega)).lower
      ⟨a.val,by have := a.isLt; omega⟩)
  have content := node_content s h ready.args (heap (2*node)) (heap (2*node+1))
    ready.height ready.mask inputs aligned separate
  have evaluated := congrArg (fun computation : OracleComp World Output => (checkEvaluation oracle computation).1) content
  simpa only [check_evaluation_bind,check_evaluation_pure,ready.target,
    heap_address_numeric node (by have := ready.small; omega),heapDigest,parentValue,parentDigestTrace] using evaluated

theorem node_content_step (oracle : Oracle) (s : MachineState) (heap : Nat → BitVec 238)
    (h : Height) (node : Nat) (positive : 0 < node) (ready : HeapNodeReady s h node)
    (tree : (heap node).setWidth 256 = parentValue oracle h (heap (2*node)) (heap (2*node+1)))
    (prior : HeapContent s heap node) :
    HeapContent (checkEvaluation oracle (nodeTrace h s)).1 heap (node-1) := by
  let out := (checkEvaluation oracle (nodeTrace h s)).1
  have reached := check_evaluation_support oracle (nodeTrace h s)
  constructor
  intro j larger small
  by_cases same : j = node
  · subst j
    exact (node_evaluation_value oracle s heap h node positive ready prior).trans tree.symm
  · have later : node < j := by omega
    apply Eq.trans _ (prior.nodes j later small)
    apply read_digest_congr out s (heapBase+32*j) (by unfold heapBase; omega)
    intro i short
    have outside := heap_word_outside j i small (by omega)
    have preserved := node_memory_outside s out h ready.args reached
      (heapAddress j+BitVec.ofNat 64 (8*i)) outside ?_
    · simpa only [heapAddress,BitVec.ofNat_add] using preserved
    · intro k equal
      rw [ready.target] at equal
      have numeric := congrArg BitVec.toNat equal
      rw [heap_word_numeric j i small (by omega),
        heap_word_numeric node k.val (by have := ready.small; omega) (by have := k.isLt; omega)] at numeric
      have hk := k.isLt
      omega

end CommitGolfCandidate.Chained.Native
