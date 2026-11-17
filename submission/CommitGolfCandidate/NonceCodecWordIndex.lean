import CommitGolfCandidate.NonceCodecIndex
import CommitGolfCandidate.NonceCompactPrefixMemory

namespace CommitGolfCandidate
set_option maxHeartbeats 400000

private theorem source_word_next (index : Nat) :
    noncePackedSourceWord (67+index)=68+noncePackedSourceWord index := by
  have quotient : (67+index)/67=1+index/67 := by omega
  have remainder : (67+index)%67=index%67 := by omega
  simp only [noncePackedSourceWord, quotient, remainder]
  split <;> omega

theorem nonce_codec_word_index (count index : Nat) :
    NonceCodec.sourceOffset count index=
      if index<536*count then
        8*noncePackedSourceWord (index/8)+index%8 else index+8*count := by
  induction count generalizing index with
  | zero => simp [NonceCodec.sourceOffset]
  | succ count ih =>
    by_cases first : index<24
    · have prefixBound : index<536*(count+1) := by omega
      have quotient : index/8/67=0 := by omega
      have remainder : (index/8)%67=index/8 := by omega
      have nonce : index/8<3 := by omega
      simp only [NonceCodec.sourceOffset, if_pos first, if_pos prefixBound,
        noncePackedSourceWord, quotient, remainder, if_pos nonce]
      omega
    · by_cases sibling : index<536
      · have prefixBound : index<536*(count+1) := by omega
        have quotient : index/8/67=0 := by omega
        have remainder : (index/8)%67=index/8 := by omega
        have nonce : ¬index/8<3 := by omega
        simp only [NonceCodec.sourceOffset, if_neg first, if_pos sibling, if_pos prefixBound,
          noncePackedSourceWord, quotient, remainder, if_neg nonce]
        omega
      · simp only [NonceCodec.sourceOffset, if_neg first, if_neg sibling, ih]
        have division : index/8=67+(index-536)/8 := by omega
        have remainder : index%8=(index-536)%8 := by omega
        have prefixBound : index<536*(count+1) ↔ index-536<536*count := by omega
        by_cases inside : index-536<536*count
        · rw [if_pos inside, if_pos (prefixBound.mpr inside), division, source_word_next, remainder]
          omega
        · rw [if_neg inside, if_neg (by simpa only [prefixBound] using inside)]
          omega

end CommitGolfCandidate
