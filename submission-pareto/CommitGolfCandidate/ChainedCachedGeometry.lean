import CommitGolfCandidate.ChainedCachedPayload

/-! Canonical widths of the cached siblings and cap words copied by the opener. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Opening
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

theorem cached_lower_node_range (index : Index) (h : Fin 15) :
    heightCount ⟨h.val,by omega⟩≤(lowerNode index (h.val+1) ^^^ 1) ∧
    (lowerNode index (h.val+1) ^^^ 1)<2*heightCount ⟨h.val,by omega⟩ := by
  have half : (lowerNode index (h.val+1) ^^^ 1)/2=lowerNode index (h.val+1)/2 := by
    simp only [Nat.xor_div_two,show 1/2=0 from rfl,Nat.xor_zero]
  have bound := index.isLt
  fin_cases h <;> norm_num [heightCount,lowerNode,LENGTH,LOG_LENGTH] at half bound ⊢ <;> omega

theorem cached_lower_width (oracle : Oracle) (leaves : Nat → BitVec 238) (index : Index) (h : Fin 15) :
    (referenceHeap oracle leaves (lowerNode index (h.val+1) ^^^ 1)).toNat<2^(width ⟨h.val,by omega⟩) :=
  reference_heap_width oracle leaves _ _ (cached_lower_node_range index h).1 (cached_lower_node_range index h).2

theorem cached_footer_width (oracle : Oracle) (leaves : Nat → BitVec 238) (node : Nat) (small : node<512) :
    (referenceHeap oracle leaves node).toNat<2^(InteriorCodec.footerWidth node) := by
  by_cases leaf : 256≤node
  · have bounded := reference_heap_width oracle leaves ⟨15,by decide⟩ node leaf small
    norm_num [width] at bounded
    convert bounded using 1 <;> norm_num [InteriorCodec.footerWidth,leaf]
  · simpa only [InteriorCodec.footerWidth,ite_eq_right leaf] using (referenceHeap oracle leaves node).isLt

end CommitGolfCandidate.Chained.Native
