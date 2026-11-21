import CommitGolfCandidate.ChainedTailPlan

/-! The native traversal's byte-write plan equals the generic packed tail. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf

def finishTailBytes (bits : List Bool) : Proof :=
  if bits.length=0 then [] else [tailBitsWord 8 bits]

theorem packed_bits_single (bits : List Bool) (positive : 0<bits.length) (small : bits.length≤8) :
    packedBits bits=[tailBitsWord 8 bits] := by
  have size : (packedBits bits).length=1 := by rw [packed_bits_length]; omega
  apply List.ext_getElem
  · simpa using size
  intro index inside right
  have zero : index=0 := by omega
  subst index
  have data := packed_bits_byte bits 0
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem inside,Option.getD_some,
    Nat.mul_zero,List.drop_zero,List.getElem_cons_zero] using data

theorem packed_bits_finish (bits : List Bool) (pending : bits.length<8) : packedBits bits=finishTailBytes bits := by
  by_cases empty : bits.length=0
  · have same : bits=[] := List.length_eq_zero_iff.mp empty
    subst bits
    rfl
  · rw [finishTailBytes,ite_eq_right empty]
    exact packed_bits_single bits (by omega) (by omega)

theorem tail_word_take_eight (bits : List Bool) : tailBitsWord 8 (bits.take 8)=tailBitsWord 8 bits := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  rw [tail_bits_word_bit 8 _ bit inside,tail_bits_word_bit 8 _ bit inside]
  simp [List.getD_eq_getElem?_getD,inside]

theorem tail_word_append_eight (front back : List Bool) (long : 8≤front.length) :
    tailBitsWord 8 (front++back)=tailBitsWord 8 front := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  rw [tail_bits_word_bit 8 _ bit inside,tail_bits_word_bit 8 _ bit inside]
  exact List.getD_append front back false bit (by omega)

theorem packed_bits_pop (bits : List Bool) (long : 8≤bits.length) :
    packedBits bits=tailBitsWord 8 bits::packedBits (bits.drop 8) := by
  have size : (bits.take 8).length=8 := by simp only [List.length_take]; omega
  have data := packed_bits_append (bits.take 8) (bits.drop 8) (by omega)
  rw [List.take_append_drop,packed_bits_single (bits.take 8) (by omega) (by omega),tail_word_take_eight] at data
  exact data

theorem tail_plan_packed (rows : List (List Bool)) (front : List Bool) (pending : front.length<8)
    (small : ∀ row ∈ rows, row.length≤6) :
    tailPlanBytes front rows++finishTailBytes (tailPlanCarry front rows)=packedBits (front++rows.flatten) := by
  induction rows generalizing front with
  | nil => simpa [tailPlanBytes,tailPlanCarry] using (packed_bits_finish front pending).symm
  | cons back rows ih =>
    have bound := small back (by simp)
    have rest := ih (nextTailBits front back) (next_tail_pending front back pending bound)
      (fun row member => small row (by simp [member]))
    by_cases fits : (front++back).length<8
    · simpa only [tailPlanBytes,tailPlanCarry,nextTailBits,fits,↓reduceIte,List.flatten_cons,List.append_assoc] using rest
    · have long : 8≤(front++back).length := by omega
      have bound : 8≤front.length+back.length := by simpa only [List.length_append] using long
      have pop := packed_bits_pop ((front++back)++rows.flatten) (by simp only [List.length_append]; omega)
      rw [tail_word_append_eight _ _ long] at pop
      simp only [tailPlanBytes,tailPlanCarry,fits,↓reduceIte,List.cons_append,List.flatten_cons]
      rw [←List.append_assoc,pop]
      congr 1
      simpa only [nextTailBits,fits,↓reduceIte,List.drop_append_of_le_length long] using rest

end CommitGolfCandidate.Chained.Native
