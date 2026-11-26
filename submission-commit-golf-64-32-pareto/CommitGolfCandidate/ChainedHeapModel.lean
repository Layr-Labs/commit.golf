import CommitGolfCandidate.ChainedParentsContent
import Mathlib.Data.Nat.Log

/-! A canonical variable-width reference tree for the native chained heap. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
attribute [local irreducible] checkEvaluation readBuffer

theorem final_value_fits (h : Height) (value : Output) : (finalValue h value).toNat < 2^238 := by
  have bounded := width_upper h
  have bound : value.toNat % 2^(width h) < 2^238 :=
    (Nat.mod_lt _ (by positivity)).trans_le (Nat.pow_le_pow_right (by decide) bounded)
  have larger : 2^238 ≤ 2^256 := Nat.pow_le_pow_right (by decide) (by decide)
  simpa only [finalValue,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (bound.trans_le larger)] using bound

theorem parent_value_fits (oracle : Oracle) (h : Height) (left right : BitVec 238) :
    (parentValue oracle h left right).toNat < 2^238 := by
  simp only [parentValue,parentDigestTrace,check_evaluation_bind,check_evaluation_pure]
  exact final_value_fits h _

theorem parent_value_extend (oracle : Oracle) (h : Height) (left right : BitVec 238) :
    (BitVec.ofNat 238 (parentValue oracle h left right).toNat).setWidth 256 = parentValue oracle h left right := by
  have small := parent_value_fits oracle h left right
  have larger : 2^238 ≤ 2^256 := Nat.pow_le_pow_right (by decide) (by decide)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt (small.trans_le larger)]

noncomputable def referenceNode (oracle : Oracle) (leaves : Nat → BitVec 238) : Nat → Nat → BitVec 238
  | 0,node => leaves node
  | height+1,node => BitVec.ofNat 238 (parentValue oracle ⟨height%24,Nat.mod_lt _ (by decide)⟩
      (referenceNode oracle leaves height (2*node)) (referenceNode oracle leaves height (2*node+1))).toNat

noncomputable def referenceHeap (oracle : Oracle) (leaves : Nat → BitVec 238) (node : Nat) : BitVec 238 :=
  referenceNode oracle leaves (24-Nat.log2 node) node

theorem heap_node_log (h : Height) (node : Nat) (lower : heightCount h ≤ node) (upper : node < 2*heightCount h) :
    Nat.log2 node = 23-h.val := by
  have positive := (height_count_bounds h).1.trans_le lower
  rw [Nat.log2_eq_log_two]
  apply (Nat.log_eq_iff (Or.inr ⟨by decide,by omega⟩)).2
  constructor
  · exact lower
  · simpa only [heightCount,Nat.pow_succ,Nat.mul_comm] using upper

theorem heap_child_log (node : Nat) (positive : 0 < node) (bit : Nat) (short : bit < 2) :
    Nat.log2 (2*node+bit) = Nat.log2 node+1 := by
  have lo : 2^(Nat.log2 node) ≤ node := (Nat.le_log2 (by omega)).mp (Nat.le_refl _)
  have hi : node < 2^(Nat.log2 node+1) := by
    by_contra absent
    have impossible : Nat.log2 node+1 ≤ Nat.log2 node := (Nat.le_log2 (by omega)).mpr (by omega)
    omega
  rw [Nat.log2_eq_log_two]
  apply (Nat.log_eq_iff (Or.inl (by omega))).2
  rw [Nat.pow_succ,Nat.pow_succ]
  constructor <;> omega

theorem reference_heap_tree (oracle : Oracle) (leaves : Nat → BitVec 238) :
    ChainedTree oracle (referenceHeap oracle leaves) := by
  intro h node lower upper
  have hsmall := h.isLt
  have positive := (height_count_bounds h).1.trans_le lower
  have log := heap_node_log h node lower upper
  have leftlog := heap_child_log node positive 0 (by decide)
  have rightlog := heap_child_log node positive 1 (by decide)
  simp only [Nat.add_zero] at leftlog
  have height : 24-Nat.log2 node = h.val+1 := by omega
  have leftheight : 24-Nat.log2 (2*node) = h.val := by omega
  have rightheight : 24-Nat.log2 (2*node+1) = h.val := by omega
  have tag : (⟨h.val%24,Nat.mod_lt _ (by decide)⟩ : Height) = h :=
    Fin.ext (Nat.mod_eq_of_lt hsmall)
  simp only [referenceHeap,height,leftheight,rightheight,referenceNode,tag]
  exact parent_value_extend oracle h _ _

theorem reference_heap_leaf (oracle : Oracle) (leaves : Nat → BitVec 238) (node : Nat)
    (lower : 2^24 ≤ node) (upper : node < 2^25) : referenceHeap oracle leaves node = leaves node := by
  have log : Nat.log2 node = 24 := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.log_eq_iff (Or.inl (by decide))).2 ⟨lower,upper⟩
  simp only [referenceHeap,log,Nat.sub_self,referenceNode]

theorem reference_heap_initial (oracle : Oracle) (leaves : Nat → BitVec 238) (s : MachineState)
    (initial : ∀ node, 2^24 ≤ node → node < 2^25 → heapDigest s node = (leaves node).setWidth 256) :
    HeapContent s (referenceHeap oracle leaves) (2^24-1) := by
  constructor
  intro node larger small
  rw [reference_heap_leaf oracle leaves node (by omega) small]
  exact initial node (by omega) small

theorem parent_levels_reference (oracle : Oracle) (leaves : Nat → BitVec 238) (s : MachineState)
    (ready : HeapLevelReady s (heightAt 24) (heightCount (heightAt 24)))
    (initial : ∀ node, 2^24 ≤ node → node < 2^25 → heapDigest s node = (leaves node).setWidth 256) :
    HeapContent (checkEvaluation oracle (parentLevels 24 s)).1 (referenceHeap oracle leaves) 0 := by
  apply parent_levels_content oracle _ (reference_heap_tree oracle leaves) 24 (by decide) (by decide) s ready
  have count : 2*heightCount (heightAt 24)-1 = 2^24-1 := by decide +kernel
  rw [count]
  exact reference_heap_initial oracle leaves s initial

end CommitGolfCandidate.Chained.Native
