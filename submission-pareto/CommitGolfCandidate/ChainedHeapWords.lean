import CommitGolfCandidate.ChainedDeliveredCommit
import CommitGolfCandidate.CheckEvaluation

/-! Serialization of cached 238-bit heap nodes into the native child-word ABI. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def heapDigest (s : MachineState) (node : Nat) : Output := readBuffer s (heapBase+32*node) 32

structure HeapContent (s : MachineState) (heap : Nat → BitVec 238) (remaining : Nat) : Prop where
  nodes : ∀ node, remaining < node → node < 2^25 → heapDigest s node = (heap node).setWidth 256

theorem heap_address_numeric (node : Nat) (small : node < 2^25) :
    (heapAddress node).toNat = heapBase+32*node := by
  have numeric := heap_word_numeric node 0 small (by decide)
  change (heapAddress node+BitVec.ofNat 64 0).toNat = heapBase+32*node+0 at numeric
  simpa using numeric

theorem heap_read_word (s : MachineState) (node word : Nat) (short : word < 4) :
    s.getMem (heapAddress node+BitVec.ofNat 64 (8*word)) =
      (heapDigest s node).extractLsb' (64*word) 64 := by
  have extracted := read_digest_word s (heapBase+32*node) word (by unfold heapBase; omega) short
  rw [BitVec.ofNat_add] at extracted
  exact extracted.symm

theorem child_word_extended (value : BitVec 238) (word : Nat) (short : word < 4) :
    (value.setWidth 256).extractLsb' (64*word) 64 = childWord value word := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [childWord,BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,
    show bit < 64 by omega,decide_true,Bool.true_and,show 64*word+bit < 256 by omega]

theorem heap_child_address (node word : Nat) (lower : 4 ≤ word) :
    heapAddress (2*node)+BitVec.ofNat 64 (8*word) =
      heapAddress (2*node+1)+BitVec.ofNat 64 (8*(word-4)) := by
  unfold heapAddress
  rw [←BitVec.ofNat_add,←BitVec.ofNat_add]
  congr 1
  omega

theorem heap_child_words (s : MachineState) (heap : Nat → BitVec 238) (node : Nat)
    (positive : 0 < node) (small : node < 2^24) (prior : HeapContent s heap node) :
    ∀ k : Fin 8, s.getMem (heapAddress (2*node)+BitVec.ofNat 64 (8*k.val)) =
      if k.val < 4 then childWord (heap (2*node)) k.val else childWord (heap (2*node+1)) (k.val-4) := by
  intro k
  by_cases left : k.val < 4
  · rw [ite_eq_left left,heap_read_word s (2*node) k.val left,
      prior.nodes (2*node) (by omega) (by omega),child_word_extended _ _ left]
  · have short : k.val-4 < 4 := by have := k.isLt; omega
    rw [ite_eq_right left,heap_child_address node k.val (by omega),
      heap_read_word s (2*node+1) (k.val-4) short,
      prior.nodes (2*node+1) (by omega) (by omega),child_word_extended _ _ short]

end CommitGolfCandidate.Chained.Native
