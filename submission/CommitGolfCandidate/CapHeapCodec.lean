import CommitGolfCandidate.CapHeapView

namespace CommitGolfCandidate
open CommitGolf
set_option maxHeartbeats 200000

theorem cap_heap_view_as_view (roots : Nat → Digest) (marked : Nat → Bool)
    (height node : Nat) :
    capHeapView roots marked height node =
      capView (capHeapTree roots height node)
        (fun offset => marked (node*2^height+offset)) := by
  induction height generalizing node with
  | zero =>
      simp only [capHeapView, capHeapTree, capView, Nat.pow_zero, Nat.mul_one,
        Nat.add_zero]
  | succ height ih =>
      simp only [capHeapView, capHeapTree, capView, ih]
      congr 2
      · funext offset
        congr 1
        rw [Nat.pow_succ]
        ring
      · funext offset
        congr 1
        rw [Nat.pow_succ]
        ring

theorem cap_heap_codec (compress : Compression) (roots : Nat → Digest)
    (marked : Nat → Bool) (height node : Nat) (suffix : List Digest) :
    capDecode compress (capHeapView roots marked height node)
      (capProof compress (capHeapTree roots height node)
        (capHeapView roots marked height node) ++ suffix) =
      some ((capHeapTree roots height node).root compress, suffix) := by
  rw [cap_heap_view_as_view]
  exact cap_codec compress _ _ suffix

end CommitGolfCandidate
