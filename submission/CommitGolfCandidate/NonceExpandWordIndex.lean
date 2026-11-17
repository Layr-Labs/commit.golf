import CommitGolfCandidate.NonceCodecExpandIndex
import CommitGolfCandidate.NonceExpandSuffixMemory

/-! The byte expansion selector matches the concrete word expansion,
including inserted padding and the relocated footer. -/
namespace CommitGolfCandidate
set_option maxHeartbeats 500000
set_option maxRecDepth 8192

private theorem expanded_word_next (index : Nat) :
    nonceExpandedSourceWord (68+index)=67+nonceExpandedSourceWord index := by
  have quotient : (68+index)/68=1+index/68 := by omega
  have remainder : (68+index)%68=index%68 := by omega
  simp only [nonceExpandedSourceWord,quotient,remainder]
  split <;> omega

theorem nonce_expand_word_index (count index : Nat) :
    NonceCodec.expandedSource count index=
      if index<544*count then
        if (index/8)%68=3 then none else
          some (8*nonceExpandedSourceWord (index/8)+index%8)
      else some (index-8*count) := by
  induction count generalizing index with
  | zero => simp [NonceCodec.expandedSource]
  | succ count ih =>
    by_cases first : index<24
    · have prefixBound : index<544*(count+1) := by omega
      have quotient : index/8/68=0 := by omega
      have remainder : (index/8)%68=index/8 := by omega
      have nonce : index/8<3 := by omega
      simp only [NonceCodec.expandedSource,if_pos first,if_pos prefixBound,
        nonceExpandedSourceWord,quotient,remainder,if_pos nonce,if_neg (by omega : index/8 ≠ 3)]
      congr 1; omega
    · by_cases padding : index<32
      · have prefixBound : index<544*(count+1) := by omega
        have remainder : (index/8)%68=3 := by omega
        simp only [NonceCodec.expandedSource,if_neg first,if_pos padding,if_pos prefixBound,remainder,ite_true]
      · by_cases sibling : index<544
        · have prefixBound : index<544*(count+1) := by omega
          have quotient : index/8/68=0 := by omega
          have remainder : (index/8)%68=index/8 := by omega
          have nonce : ¬index/8<3 := by omega
          simp only [NonceCodec.expandedSource,if_neg first,if_neg padding,if_pos sibling,
            if_pos prefixBound,nonceExpandedSourceWord,quotient,remainder,if_neg nonce,
            if_neg (by omega : index/8 ≠ 3)]
          congr 1; omega
        · simp only [NonceCodec.expandedSource,if_neg first,if_neg padding,if_neg sibling,ih]
          have division : index/8=68+(index-544)/8 := by omega
          have remainder : index%8=(index-544)%8 := by omega
          have wordRemainder : (index/8)%68=((index-544)/8)%68 := by omega
          have prefixBound : index<544*(count+1) ↔ index-544<544*count := by omega
          by_cases inside : index-544<544*count
          · rw [if_pos inside,if_pos (prefixBound.mpr inside),wordRemainder]
            by_cases zeroWord : ((index-544)/8)%68=3
            · simp only [if_pos zeroWord,Option.map_none]
            · simp only [if_neg zeroWord,Option.map_some]
              rw [division,expanded_word_next,remainder]
              congr 1; omega
          · rw [if_neg inside,if_neg (by simpa only [prefixBound] using inside)]
            simp only [Option.map_some]
            congr 1; omega
end CommitGolfCandidate
