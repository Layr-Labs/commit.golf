import CommitGolfCandidate.Layout2CapCodec
import CommitGolfCandidate.Layout2CapChecked
namespace CommitGolfCandidate.Layout2.Cap
open CommitGolf
theorem dec_valid : ValidTable dec := fun m lo hi i h=>(checked_entry m i lo hi h).1
theorem enc_valid : ValidTable enc := fun m lo hi i h=>(checked_entry m i lo hi h).2.1
theorem dec_inverse : Inverse dec enc := fun m lo hi i h=>(checked_entry m i lo hi h).2.2.1
theorem enc_inverse : Inverse enc dec := fun m lo hi i h=>(checked_entry m i lo hi h).2.2.2.1
theorem decode_encode (p P) (good : Good p.card P.length) : decoder p (encoder p P)=P := by
  unfold decoder encoder
  rw [inverse dec_valid dec_inverse _ _ (by simpa using good)]
  exact Quartet.decode_encode p P good.1
theorem encode_decode (p P) (good : Good p.card P.length) : encoder p (decoder p P)=P := by
  unfold decoder encoder
  rw [Quartet.encode_decode _ _ (by simpa using good.1),inverse enc_valid enc_inverse _ _ good]
end CommitGolfCandidate.Layout2.Cap
