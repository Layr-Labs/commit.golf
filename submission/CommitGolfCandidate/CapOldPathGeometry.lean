import CommitGolfCandidate.CapSiblingRepresentative
import CommitGolfCandidate.OpeningOutput

/-! A requested leaf in the sibling cap subtree supplies exactly the old
opening sibling at level 17+height. The finite geometric bound is ordinary
kernel-checked decide; the original full index is handled algebraically. -/
namespace CommitGolfCandidate
open CommitGolf
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

private theorem sibling_layer_bounds : ∀ height : Fin 7, ∀ node : Fin 256,
    128 ≤ node.val*2^height.val →
    (node.val+1)*2^height.val ≤ 256 →
    1 < node.val ∧
      128 ≤ (node.val ^^^ 1)*2^height.val ∧
      ((node.val ^^^ 1)+1)*2^height.val ≤ 256 := by
  decide

theorem cap_old_path_quotient (index : Index) (height : Nat) :
    (LENGTH+index.val)/2^(17+height) =
      (128+(capGroup index).val)/2^height := by
  rw [pow_add,← Nat.div_div_eq_div_mul]
  have first : (LENGTH+index.val)/2^17 = 128+(capGroup index).val := by
    change (16777216+index.val)/131072 = 128+index.val/131072
    omega
  rw [first]

theorem cap_unknown_old_sibling (positions : Positions) (height node : Nat)
    (heightBound : height < 7)
    (lower : 128 ≤ node*2^height) (upper : (node+1)*2^height ≤ 256)
    (parent : capOpenRequestedMarks positions (node/2)=true)
    (absent : capOpenRequestedMarks positions node=false) :
    ∃ ordinal < positions.card,
      (((LENGTH+openingIndex positions ordinal)/2^(17+height)) ^^^ 1)=node := by
  have power : 0 < 2^height := Nat.two_pow_pos height
  have nodeBound : node < 256 := by nlinarith
  obtain ⟨positive,siblingLower,siblingUpper⟩ :=
    sibling_layer_bounds ⟨height,heightBound⟩ ⟨node,nodeBound⟩ lower upper
  have siblingMarked := cap_sibling_marked
    (capOpenMarksSeen (capOpenRequestedIndices positions) positions.card)
    node positive nodeBound parent absent
  obtain ⟨index,member,left,right⟩ :=
    cap_requested_descendant positions height (node ^^^ 1)
      siblingLower siblingUpper siblingMarked
  obtain ⟨ordinal,inside,entry⟩ :=
    List.mem_iff_getElem.mp
      (show index ∈ positions.sort (· ≤ ·) by
        simpa only [Finset.mem_sort] using member)
  have present : ordinal < positions.card := by
    simpa only [Finset.length_sort] using inside
  refine ⟨ordinal,present,?_⟩
  have selected : openingIndex positions ordinal=index.val := by
    simp only [openingIndex,dif_pos present,entry]
  rw [selected,cap_old_path_quotient,
    Nat.div_eq_of_lt_le left right,Nat.xor_xor_cancel_right]

end CommitGolfCandidate
