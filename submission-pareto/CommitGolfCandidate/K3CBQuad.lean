import CommitGolfCandidate.K3CBDefs
import CommitGolfCandidate.K3CUUnits

/-!
# The stored group replies are the model's quartet calls

`replyWord g` (where the body leaves the reply of quartet `g`) is CU's `groupReplyWord g`, and the
reply the body computes on the record window `0^9 ‖ d0 d1 d2 d3` is the model's
`π (quartetEncode (quartetPayload d g))`.
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuartetCommit (qSource)
set_option maxRecDepth 8192

theorem reply_word_eq (g : Nat) : groupReplyWord g=replyWord g := by
  unfold groupReplyWord replyWord unitBase unitFirst unitStride cellFirst qSource
  split <;> omega

/-- One word of the record window against the model's encoding. -/
theorem quad_window_word (o : Oracle) (k : BitVec 192) (msg : Message) (g : Nat) (w : Fin 25) :
    quartetWindow o k msg g w=replyWords (quartetEncode (Quartet.quartetPayload
      (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) msg (chainSalts o k)) g)) w := by
  have hw := w.isLt
  unfold quartetWindow
  by_cases z : w.val<9
  · rw [if_pos z,quad_word_zero _ _ z]
  · rw [if_neg z]
    unfold Quartet.quartetPayload
    rw [quad_word_leaf _ _ _ _ w (by omega)]
    unfold digestOf leafVal Quartet.leafAt value
    have q : (w.val-9)/4=0 ∨ (w.val-9)/4=1 ∨ (w.val-9)/4=2 ∨ (w.val-9)/4=3 := by omega
    rcases q with q|q|q|q <;> simp only [q,Fin.val_mk,↓reduceIte,Nat.reduceEqDiff,Nat.add_zero] <;> rfl

/-- The quartet reply the body stores is the model's group call on the record window. -/
theorem quartet_reply_model (o : Oracle) (k : BitVec 192) (msg : Message) (g : Nat) :
    quartetReply o k msg g=o.permutation (quartetEncode (Quartet.quartetPayload
      (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) msg (chainSalts o k)) g)) := by
  have win : quartetWindow o k msg g=replyWords (quartetEncode (Quartet.quartetPayload
      (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) msg (chainSalts o k)) g)) := by
    funext w
    exact quad_window_word o k msg g w
  unfold quartetReply
  rw [win]
  exact congrArg (fun x : BitVec 1600 => o.permutation x) (reply_pack _)

end TwoPermutationPrototype.Grouped
