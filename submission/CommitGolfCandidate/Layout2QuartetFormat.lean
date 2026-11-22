import CommitGolfCandidate.Layout2QuartetCodec
namespace CommitGolfCandidate.Layout2.Quartet
open CommitGolf
def normalize (p : Positions) := transform false p.card (selectors p)
def denormalize (p : Positions) := transform true p.card (selectors p)
@[simp] theorem normalize_length (p P) : (normalize p P).length=P.length := length_transform ..
@[simp] theorem denormalize_length (p P) : (denormalize p P).length=P.length := length_transform ..
theorem normalize_denormalize (p P) : normalize p (denormalize p P)=P := transform_inverse true ..
theorem denormalize_normalize (p P) : denormalize p (normalize p P)=P := transform_inverse false ..
theorem decoder_suffix (p P i) (cap : 534*p.card ≤ i) (inside : i<P.length) :
    (decoder p P)[i]?.getD 0=P[i]?.getD 0 := by
  unfold decoder
  rw [convert_read _ _ _ _ (by simpa using inside),convertAt,if_neg (by omega)]
  exact suffix _ _ _ _ _ cap inside
theorem encoder_suffix (p P i) (cap : 534*p.card ≤ i) (inside : i<P.length) :
    (encoder p P)[i]?.getD 0=P[i]?.getD 0 := by
  unfold encoder
  rw [suffix _ _ _ _ _ cap (by simpa using inside),convert_read _ _ _ _ inside,convertAt,if_neg (by omega)]
end CommitGolfCandidate.Layout2.Quartet
