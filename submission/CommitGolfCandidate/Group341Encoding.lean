import CommitGolfCandidate.Programs

/-! The fixed literal image equals the assembler, and its repeated triples have a
constant-time indexed description for kernel instruction-fetch checking. -/
namespace CommitGolfCandidate
open CommitGolf
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem group341_head_length : group341HeadWords.length=166 := rfl

theorem group341_body_length : group341BodyWords.length=16368 := by
  simp only [group341BodyWords,List.length_ofFn]

theorem group341_image_length : group341ImageWords.length=16537 := by
  simp only [group341ImageWords,List.length_append,group341_head_length,group341_body_length,
    List.length_cons,List.length_nil]

/-- The independently emitted literal words are exactly the intended RV64 assembler output. -/
theorem group341_assembly_matches_literal : assemble (commitCode 24)=group341ImageWords := by
  decide

/-- Every slot in the repeated body is the selected word of its parent triple. -/
theorem group341_main_word (block slot : Nat) (bounded : block<5456) (word : slot<3) :
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

/-- The branch and final jump follow all 16368 repeated body words. -/
theorem group341_end_word (slot : Nat) :
    group341ImageWords[16534+slot]?=([9835619,3995005039,2207187055] : List (BitVec 32))[slot]? := by
  unfold group341ImageWords
  rw [List.getElem?_append_right (by rw [group341_head_length];omega),group341_head_length]
  rw [show 16534+slot-166=16368+slot by omega]
  rw [List.getElem?_append_right (by rw [group341_body_length];omega),group341_body_length]
  rw [show 16368+slot-16368=slot by omega]

end CommitGolfCandidate
