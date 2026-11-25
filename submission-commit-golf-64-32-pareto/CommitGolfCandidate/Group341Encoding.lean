import CommitGolfCandidate.Programs

/-! The repeated triples and the unrolled leaf block of the fixed literal image have
indexed descriptions for kernel instruction-fetch checking. The execution and
packed-artifact proofs certify the literal image. -/
namespace CommitGolfCandidate
open CommitGolf
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem group341_head_length : group341HeadWords.length=166 := rfl

theorem group341_body_length : group341BodyWords.length=251658 := by
  simp only [group341BodyWords,List.length_ofFn]

theorem unrolled_block_length : unrolledBlockWords.length=7947 := by
  simp only [unrolledBlockWords,List.length_ofFn]

theorem group341_image_length : group341ImageWords.length=259774 := by
  simp only [group341ImageWords,List.length_append,group341_head_length,group341_body_length,
    unrolled_block_length,List.length_cons,List.length_nil]

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

/-- The branch and two jumps follow all 251658 repeated body words. -/
theorem group341_end_word (slot : Nat) (bounded : slot<3) :
    group341ImageWords[251824+slot]?=([9835619,2810224751,3170934895] : List (BitVec 32))[slot]? := by
  unfold group341ImageWords
  rw [List.getElem?_append_right (by rw [group341_head_length];omega),group341_head_length]
  rw [show 251824+slot-166=251658+slot by omega]
  rw [List.getElem?_append_right (by rw [group341_body_length];omega),group341_body_length]
  rw [show 251658+slot-251658=slot by omega]
  rw [List.getElem?_append_left (by simp only [List.length_cons,List.length_nil];omega)]

/-- The unrolled leaf block follows the parent-group tail. -/
theorem unrolled_block_word_at (index : Nat) (bounded : index<7947) :
    group341ImageWords[251827+index]?=some (unrolledBlockWord index) := by
  unfold group341ImageWords
  rw [List.getElem?_append_right (by rw [group341_head_length];omega),group341_head_length]
  rw [show 251827+index-166=251658+(3+index) by omega]
  rw [List.getElem?_append_right (by rw [group341_body_length];omega),group341_body_length]
  rw [show 251658+(3+index)-251658=3+index by omega]
  rw [List.getElem?_append_right (by simp only [List.length_cons,List.length_nil];omega)]
  simp only [List.length_cons,List.length_nil]
  rw [show 3+index-(0+1+1+1)=index by omega]
  unfold unrolledBlockWords
  rw [List.getElem?_ofFn,dif_pos bounded]

end CommitGolfCandidate
