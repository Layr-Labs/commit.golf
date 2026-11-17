import CommitGolfCandidate.Programs

/-! The repeated triples of the fixed literal image have an indexed description
for kernel instruction-fetch checking. The execution and packed-artifact proofs certify the literal image. -/
namespace CommitGolfCandidate
open CommitGolf
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem group341_head_length : group341HeadWords.length=166 := rfl

theorem group341_body_length : group341BodyWords.length=251658 := by
  simp only [group341BodyWords,List.length_ofFn]

theorem t1_group_length : t1GroupWords.length=996 := rfl

theorem group341_end_length : group341EndWords.length=999 := by
  simp only [group341EndWords,List.length_cons,t1_group_length]

theorem group341_image_length : group341ImageWords.length=252823 := by
  simp only [group341ImageWords,List.length_append,group341_head_length,group341_body_length,
    group341_end_length]

/-- Every slot in the repeated body is the selected word of its parent triple. -/
theorem group341_main_word (block slot : Nat) (bounded : block<83886) (word : slot<3) :
    group341ImageWords[166+3*block+slot]?=some (group341BodyWord slot) := by
  unfold group341ImageWords
  rw [List.getElem?_append_right (by rw [group341_head_length];omega),group341_head_length]
  rw [show 166+3*block+slot-166=3*block+slot by omega]
  rw [List.getElem?_append_left (by rw [group341_body_length];omega)]
  unfold group341BodyWords
  rw [List.getElem?_ofFn,dif_pos (by omega)]
  change some (group341BodyWord (3*block+slot))=some (group341BodyWord slot)
  unfold group341BodyWord
  rw [show (3*block+slot)%3=slot by omega,Nat.mod_eq_of_lt word]

/-- The branch and final jump follow all 251658 repeated body words; the appended group follows them. -/
theorem group341_end_word (slot : Nat) :
    group341ImageWords[251824+slot]?=group341EndWords[slot]? := by
  unfold group341ImageWords
  rw [List.getElem?_append_right (by rw [group341_head_length];omega),group341_head_length]
  rw [show 251824+slot-166=251658+slot by omega]
  rw [List.getElem?_append_right (by rw [group341_body_length];omega),group341_body_length]
  rw [show 251658+slot-251658=slot by omega]

/-- Word `251827+k` of the image is word `k` of the appended group. -/
theorem t1_group_word (k : Nat) :
    group341ImageWords[251827+k]?=t1GroupWords[k]? := by
  rw [show 251827+k=251824+(k+1+1+1) by omega,group341_end_word,group341EndWords,
    List.getElem?_cons_succ,List.getElem?_cons_succ,List.getElem?_cons_succ]

end CommitGolfCandidate
