import CommitGolfCandidate.TwoPermutationHybridModel
import CommitGolfCandidate.TwoPermutationPackedParentMask

namespace TwoPermutationPrototype.Hybrid
open CommitGolf CommitGolfCandidate RV64 Sampling

theorem heap_leaf (compress : Compression) (leaves : DigestTape) (i : Index) :
    heap compress leaves (LENGTH+i.val)=leaves i := by
  have bound := i.isLt
  rw [heap, dif_neg (by omega), dif_pos (by omega)]
  exact congrArg leaves (Fin.ext (Nat.add_sub_cancel_left LENGTH i.val))

theorem raw_parent (compress : Compression) (leaves : DigestTape) (n : Nat)
    (lo : 8388608 ≤ n) (hi : n < LENGTH) :
    heap compress leaves n = compress (heap compress leaves (2*n+1) ++ heap compress leaves (2*n)) := by
  rw [heap_parent _ _ _ ⟨by omega, hi⟩, normalize, if_neg]
  · rfl
  · change ¬ n < 8388608
    omega

theorem masked_parent (compress : Compression) (leaves : DigestTape) (n : Nat)
    (lo : 0 < n) (hi : n < 8388608) :
    heap compress leaves n = projectReply (compress (heap compress leaves (2*n+1) ++ heap compress leaves (2*n))) := by
  have within : n < LENGTH := by change n < 16777216; omega
  rw [heap_parent _ _ _ ⟨lo, within⟩, normalize, if_pos]
  · rfl
  · exact hi

end TwoPermutationPrototype.Hybrid
