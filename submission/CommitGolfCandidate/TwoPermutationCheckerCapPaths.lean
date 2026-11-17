import CommitGolfCandidate.TwoPermutationCheckerPaths

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling

/-- Once the marked cap is materialized in scratch, a marked internal parent
has a trace row for its ordered child pair. Marked leaves may carry multiple
lower authentication paths for the same digest. -/
structure CapRecorded (rows : List PublicRow) (roots : Nat → BitVec 256) (marked : Nat → Prop) where
  propagate : ∀ node, 2 ≤ node → node < 512 → marked node → marked (node/2)
  hashed : ∀ node, 1 ≤ node → node < 256 → marked node →
    PublicRow.compression (roots (2*node+1) ++ roots (2*node)) (roots node) ∈ rows

theorem CapRecorded.path {rows : List PublicRow} {roots : Nat → BitVec 256} {marked : Nat → Prop}
    (cap : CapRecorded rows roots marked) (height node : Nat)
    (level : 2^height ≤ node ∧ node < 2^(height+1))
    (below : node < 512) (active : marked node) :
    RecordedPath rows node height (roots node) (roots 1) := by
  induction height generalizing node with
  | zero =>
    have root : node = 1 := by simp at level; omega
    subst node
    exact .done 1 _
  | succ height ih =>
    have slot : 2 ≤ node := by
      rw [Nat.pow_succ] at level
      have : 0 < 2^height := Nat.pow_pos (by decide)
      omega
    have levelParent : 2^height ≤ node/2 ∧ node/2 < 2^(height+1) := by
      have lower := level.1
      have upper := level.2
      rw [Nat.pow_succ] at lower upper
      omega
    have activeParent := cap.propagate node slot below active
    have call := cap.hashed (node/2) (by omega) (by omega) activeParent
    have next := ih (node/2) levelParent (by omega) activeParent
    by_cases left : node % 2 = 0
    · have child : 2*(node/2) = node := by omega
      apply RecordedPath.step (sibling := roots (2*(node/2)+1)) ?_ next
      simpa only [pathPair, ite_eq_left left, child] using call
    · have child : 2*(node/2)+1 = node := by omega
      apply RecordedPath.step (sibling := roots (2*(node/2))) ?_ next
      simpa only [pathPair, ite_eq_right left, child] using call

theorem cap_join_lower {rows : List PublicRow} {roots : Nat → BitVec 256} {marked : Nat → Prop}
    (cap : CapRecorded rows roots marked) (index : Index) (digest : BitVec 256)
    (lower : RecordedPath rows (LENGTH+index.val) 16 digest (roots ((LENGTH+index.val)/2^16)))
    (markedGroup : marked ((LENGTH+index.val)/2^16)) :
    RecordedPath rows (LENGTH+index.val) LOG_LENGTH digest (roots 1) := by
  have indexBound := index.isLt
  change index.val < 16777216 at indexBound
  have low : 256 ≤ (LENGTH+index.val)/2^16 := by change 256 ≤ (16777216+index.val)/65536; omega
  have high : (LENGTH+index.val)/2^16 < 512 := by change (16777216+index.val)/65536 < 512; omega
  exact lower.append (cap.path 8 _ ⟨low, high⟩ high markedGroup)

end TwoPermutationPrototype.Checker
