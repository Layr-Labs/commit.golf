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

theorem group341_image_length : group341ImageWords.length=253942 := by
  simp only [group341ImageWords,unrollWords,List.length_append,group341_head_length,group341_body_length,
    List.length_cons,List.length_nil,List.length_ofFn]

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

/-- The branch and final jump follow all 251658 repeated body words. -/
theorem group341_end_word (slot : Nat) (small : slot<3) :
    group341ImageWords[251824+slot]?=([9835619,2810224751,3170934895] : List (BitVec 32))[slot]? := by
  unfold group341ImageWords
  rw [List.getElem?_append_right (by rw [group341_head_length];omega),group341_head_length]
  rw [show 251824+slot-166=251658+slot by omega]
  rw [List.getElem?_append_right (by rw [group341_body_length];omega),group341_body_length]
  rw [show 251658+slot-251658=slot by omega]
  rw [List.getElem?_append_left (by simp; omega)]

theorem unroll_ofFn_length : (List.ofFn (fun i : Fin 2112 => unrollBodyWord i.val)).length=2112 :=
  List.length_ofFn

/-- Every relocated body slot is the selected word of the 33-word body. -/
theorem unroll_body_word (body slot : Nat) (bounded : body<64) (word : slot<33) :
    group341ImageWords[251827+33*body+slot]?=some (unrollBodyWord slot) := by
  unfold group341ImageWords
  rw [List.getElem?_append_right (by rw [group341_head_length];omega),group341_head_length]
  rw [List.getElem?_append_right (by rw [group341_body_length];omega),group341_body_length]
  rw [List.getElem?_append_right (by simp;omega)]
  simp only [List.length_cons,List.length_nil]
  unfold unrollWords
  rw [List.getElem?_append_left (by rw [unroll_ofFn_length];omega)]
  rw [List.getElem?_ofFn]
  simp only [show 251827+33*body+slot-166-251658-3=33*body+slot by omega]
  rw [dif_pos (by omega)]
  change some (unrollBodyWord (33*body+slot))=some (unrollBodyWord slot)
  unfold unrollBodyWord
  rw [show (33*body+slot)%33=slot by omega,Nat.mod_eq_of_lt word]

theorem unroll_end_word (slot : Nat) (small : slot<3) :
    group341ImageWords[253939+slot]?=([23848035,2717941871,4020228207] : List (BitVec 32))[slot]? := by
  unfold group341ImageWords
  rw [List.getElem?_append_right (by rw [group341_head_length];omega),group341_head_length]
  rw [List.getElem?_append_right (by rw [group341_body_length];omega),group341_body_length]
  rw [List.getElem?_append_right (by simp;omega)]
  simp only [List.length_cons,List.length_nil]
  unfold unrollWords
  rw [List.getElem?_append_right (by rw [unroll_ofFn_length];omega),unroll_ofFn_length]
  congr 1
  omega

end CommitGolfCandidate
