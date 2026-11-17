import CommitGolfCandidate.NonceCodecLength

namespace CommitGolfCandidate.NonceCodec
set_option maxHeartbeats 400000

def sourceOffset : Nat → Nat → Nat
  | 0, index => index
  | count+1, index => if index<24 then index else if index<536 then index+8
      else 544+sourceOffset count (index-536)

theorem compact_index {α : Type} (count : Nat) (bytes : List α)
    (enough : 544*count ≤ bytes.length) (index : Nat) :
    (compact count bytes)[index]?=bytes[sourceOffset count index]? := by
  induction count generalizing bytes index with
  | zero => rfl
  | succ count ih =>
    have firstLength : (bytes.take 24).length=24 := by
      simp only [List.length_take]
      omega
    have siblingsLength : ((bytes.drop 32).take 512).length=512 := by
      simp only [List.length_take, List.length_drop]
      omega
    have tailEnough : 544*count ≤ (bytes.drop 544).length := by
      simp only [List.length_drop]
      omega
    rw [compact, List.append_assoc]
    by_cases first : index<24
    · rw [List.getElem?_append_left (by omega)]
      simp only [List.getElem?_take, if_pos first, sourceOffset]
    · rw [List.getElem?_append_right (by omega), firstLength]
      by_cases sibling : index<536
      · rw [List.getElem?_append_left (by omega)]
        simp only [List.getElem?_take, if_pos (by omega : index-24<512), List.getElem?_drop,
          sourceOffset, if_neg first, if_pos sibling]
        congr 1
        omega
      · rw [List.getElem?_append_right (by omega), siblingsLength]
        have tailIndex : index-24-512=index-536 := by omega
        rw [tailIndex, ih _ tailEnough, List.getElem?_drop]
        simp only [sourceOffset, if_neg first, if_neg sibling]

end CommitGolfCandidate.NonceCodec
