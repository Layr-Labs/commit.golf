import CommitGolfCandidate.CapCheckRecordsCount
import CommitGolfCandidate.CapCheckFilledMarks
import CommitGolfCandidate.CapDfsSerialization

/-! The finalized mark shape is the known-leaf shape of the same collected
map used in the supported-record count. No digest or parent-hash consistency
is needed for this occupancy-only correspondence. -/
namespace CommitGolfCandidate
open CommitGolf
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_known_marks_shape (roots : CapRootMap) (height offset node : Nat)
    (address : offset + 128 = node * 2^height)
    (bounded : offset + 2^height ≤ 128) :
    capOccupied (capKnownView roots height offset) = capCheckCollectedMarks roots node ∧
      CapViewMarks (capCheckCollectedMarks roots) node (capKnownView roots height offset) := by
  induction height generalizing offset node with
  | zero =>
    have nodeEq : node = offset + 128 := by simpa using address.symm
    have nodeLower : 128 ≤ node := by omega
    have leaf : capCheckCollectedMarks roots node = (roots offset).isSome := by
      rw [capCheckCollectedMarks, cap_tree_marks_leaf _ node nodeLower, nodeEq]
      simp
    exact ⟨by simpa only [capKnownView, capOccupied] using leaf.symm,
      by simpa only [capKnownView, CapViewMarks] using leaf⟩
  | succ height ih =>
    have power : 0 < 2^height := Nat.two_pow_pos height
    have address' := address
    rw [pow_succ] at address'
    have positive : 0 < node := by nlinarith
    have internal : node < 128 := by
      have bound' := bounded
      rw [pow_succ] at bound'
      nlinarith
    have leftAddress : offset + 128 = (2*node)*2^height := by nlinarith
    have rightAddress : offset + 2^height + 128 = (2*node+1)*2^height := by nlinarith
    have leftBound : offset + 2^height ≤ 128 := by
      rw [pow_succ] at bounded
      nlinarith
    have rightBound : offset + 2^height + 2^height ≤ 128 := by
      rw [pow_succ] at bounded
      nlinarith
    obtain ⟨leftOccupied, leftMarks⟩ := ih offset (2*node) leftAddress leftBound
    obtain ⟨rightOccupied, rightMarks⟩ :=
      ih (offset+2^height) (2*node+1) rightAddress rightBound
    have parent := cap_tree_marks_parent
      (fun node => (roots (node-128)).isSome) node positive internal
    change capCheckCollectedMarks roots node =
      (capCheckCollectedMarks roots (2*node) ||
        capCheckCollectedMarks roots (2*node+1)) at parent
    have occupied : capOccupied (capKnownView roots (height+1) offset) =
        capCheckCollectedMarks roots node := by
      simp only [capKnownView, capOccupied, leftOccupied, rightOccupied]
      exact parent.symm
    exact ⟨occupied, ⟨occupied.symm, leftMarks, rightMarks⟩⟩

theorem cap_check_known_root_marks (roots : CapRootMap) :
    CapViewMarks (capCheckCollectedMarks roots) 1 (capKnownView roots 7 0) :=
  (cap_check_known_marks_shape roots 7 0 1 (by decide) (by decide)).2

end CommitGolfCandidate
