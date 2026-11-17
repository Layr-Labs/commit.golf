import CommitGolfCandidate.NonceCodec

namespace CommitGolfCandidate.NonceCodec
set_option maxHeartbeats 400000

def expandedSource : Nat → Nat → Option Nat
  | 0,index => some index
  | count+1,index => if index<24 then some index else if index<32 then none
      else if index<544 then some (index-8)
      else (expandedSource count (index-544)).map (536+·)

theorem expand_length {α : Type} (zero : α) (count : Nat) (bytes : List α)
    (enough : 536*count ≤ bytes.length) :
    (expand zero count bytes).length=bytes.length+8*count := by
  induction count generalizing bytes with
  | zero => simp [expand]
  | succ count ih =>
    have first : 24 ≤ bytes.length := by omega
    have siblings : 512 ≤ (bytes.drop 24).length := by simp only [List.length_drop]; omega
    have tailEnough : 536*count ≤ (bytes.drop 536).length := by simp only [List.length_drop]; omega
    simp only [expand,List.length_append,List.length_take,List.length_replicate,
      Nat.min_eq_left first,Nat.min_eq_left siblings,ih _ tailEnough,List.length_drop]
    omega

theorem expand_index {α : Type} (zero : α) (count : Nat) (bytes : List α)
    (enough : 536*count ≤ bytes.length) (index : Nat) :
    (expand zero count bytes)[index]?=
      match expandedSource count index with | none => some zero | some source => bytes[source]? := by
  induction count generalizing bytes index with
  | zero => rfl
  | succ count ih =>
    have firstLength : (bytes.take 24).length=24 := by simp only [List.length_take]; omega
    have siblingsLength : ((bytes.drop 24).take 512).length=512 := by
      simp only [List.length_take,List.length_drop]
      omega
    have tailEnough : 536*count ≤ (bytes.drop 536).length := by simp only [List.length_drop]; omega
    rw [expand,List.append_assoc,List.append_assoc]
    by_cases first : index<24
    · rw [List.getElem?_append_left (by omega)]
      simp only [List.getElem?_take,if_pos first,expandedSource]
    · rw [List.getElem?_append_right (by omega),firstLength]
      by_cases padding : index<32
      · rw [List.getElem?_append_left (by simp only [List.length_replicate]; omega)]
        simp only [List.getElem?_replicate,if_pos (by omega : index-24<8),
          expandedSource,if_neg first,if_pos padding]
      · rw [List.getElem?_append_right (by simp only [List.length_replicate]; omega),List.length_replicate]
        have afterPadding : index-24-8=index-32 := by omega
        rw [afterPadding]
        by_cases sibling : index<544
        · rw [List.getElem?_append_left (by omega)]
          simp only [List.getElem?_take,if_pos (by omega : index-32<512),List.getElem?_drop,
            expandedSource,if_neg first,if_neg padding,if_pos sibling]
          congr 1
          omega
        · rw [List.getElem?_append_right (by omega),siblingsLength]
          have afterRecord : index-32-512=index-544 := by omega
          rw [afterRecord,ih _ tailEnough]
          simp only [expandedSource,if_neg first,if_neg padding,if_neg sibling]
          cases selected : expandedSource count (index-544) with
          | none => rfl
          | some source => simp only [Option.map_some,List.getElem?_drop]

end CommitGolfCandidate.NonceCodec
