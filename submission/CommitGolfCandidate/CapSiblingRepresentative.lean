import CommitGolfCandidate.CapMarkDescendant
import CommitGolfCandidate.CapOpenFilledMarks

/-! Every unknown child of an occupied cap node has a requested position in
its sibling subtree. This identifies a transmitted old-path sibling using
positions alone. It neither hashes nor examines oracle replies. -/
namespace CommitGolfCandidate
open CommitGolf
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem cap_sibling_marked (leaves : Nat → Bool) (node : Nat)
    (positive : 1 < node) (bounded : node < 256)
    (parent : capTreeMarks leaves (node/2)=true)
    (absent : capTreeMarks leaves node=false) :
    capTreeMarks leaves (node ^^^ 1)=true := by
  rw [cap_tree_marks_parent leaves (node/2) (by omega) (by omega)] at parent
  by_cases even : node%2=0
  · have left : 2*(node/2)=node := by omega
    rw [left,absent,Bool.false_or] at parent
    rw [Nat.xor_one_of_even (Nat.even_iff.mpr even)]
    simpa only [left] using parent
  · have right : 2*(node/2)+1=node := by omega
    rw [right,absent,Bool.or_false] at parent
    rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega : node%2=1))]
    have left : 2*(node/2)=node-1 := by omega
    simpa only [left] using parent

theorem cap_requested_descendant (positions : Positions) (height node : Nat)
    (lower : 128 ≤ node*2^height) (upper : (node+1)*2^height ≤ 256)
    (marked : capOpenRequestedMarks positions node=true) :
    ∃ index ∈ positions,
      node*2^height ≤ 128+(capGroup index).val ∧
        128+(capGroup index).val < (node+1)*2^height := by
  obtain ⟨leaf,left,right,seen⟩ :=
    (cap_mark_descendant
      (capOpenMarksSeen (capOpenRequestedIndices positions) positions.card)
      height node lower upper).mp marked
  have count : (capOpenRequestedIndices positions).length=positions.card := by
    simp only [capOpenRequestedIndices,Finset.length_sort]
  rw [← count,cap_open_marks_seen_full] at seen
  obtain ⟨index,member,same⟩ := seen
  refine ⟨index,?_,?_,?_⟩
  · simpa only [capOpenRequestedIndices,Finset.mem_sort] using member
  · simpa only [same] using left
  · simpa only [same] using right

end CommitGolfCandidate
