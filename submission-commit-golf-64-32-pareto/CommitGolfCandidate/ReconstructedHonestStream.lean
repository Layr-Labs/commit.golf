import Std

namespace CommitGolfCandidate.Reconstruction.HonestStream

/-- Word at a little-endian word offset in a packed proof. -/
def word (stream i : Nat) := (stream >>> (64*i)) % 2^64

/-- Semantics of the checker's two-word reader, including a full-width field. -/
def get (stream cursor n : Nat) :=
  let offset := cursor % 64
  let index := cursor / 64
  let first := word stream index >>> offset
  let bits := if offset+n > 64
              then first ||| (((word stream (index+1)) <<< (64-offset)) % 2^64)
              else first
  bits % 2^n

private theorem bit_word (stream i bit : Nat) :
    (word stream i).testBit bit = (decide (bit < 64) && stream.testBit (64*i+bit)) := by
  simp only [word, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

/-- Reading the pair of adjacent loaded words extracts the specified bit field
even when it straddles a word boundary. Bits beyond the field may be arbitrary. -/
theorem get_eq (stream cursor n : Nat) (width : n ≤ 64) :
    get stream cursor n = (stream >>> cursor) % 2^n := by
  apply Nat.eq_of_testBit_eq
  intro bit
  have off : cursor % 64 < 64 := Nat.mod_lt _ (by decide)
  have splitCursor := Nat.div_add_mod cursor 64
  by_cases inside : bit < n
  · have fits : bit < 64 := by omega
    by_cases cross : cursor%64+n > 64
    · by_cases upper : 64-cursor%64 ≤ bit
      · have above : ¬ (bit + cursor%64 < 64) := by omega
        have inner : bit - (64-cursor%64) < 64 := by omega
        have idx : 64*(cursor/64+1)+(bit-(64-cursor%64)) = cursor+bit := by omega
        simp only [get, cross, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, Nat.testBit_or, ite_true, decide_true, decide_false, Bool.false_and, Bool.false_or, Bool.true_and, inside, fits,
          bit_word, upper, above, inner, idx, Nat.add_comm (cursor%64) bit]
      · have below : bit + cursor%64 < 64 := by omega
        have idx : 64*(cursor/64)+(bit+cursor%64) = cursor+bit := by omega
        simp only [get, cross, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_shiftLeft, Nat.testBit_or, ite_true, decide_true, decide_false, Bool.false_and, Bool.and_false, Bool.or_false, Bool.true_and, inside, fits,
          bit_word, upper, below, idx, Nat.add_comm (cursor%64) bit]
    · have below : bit + cursor%64 < 64 := by omega
      have idx : 64*(cursor/64)+(bit+cursor%64) = cursor+bit := by omega
      simp only [get, cross, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, ite_false, inside, decide_true, Bool.true_and, bit_word, below, idx,
        Nat.add_comm (cursor%64) bit]
  · simp [get, Nat.testBit_mod_two_pow, inside]

/-- Append a bounded unsigned field to the prefix at the cursor. -/
def append (stream cursor value : Nat) := stream ||| (value <<< cursor)

/-- The new field is preserved and every previously occupied bit is unchanged. -/
theorem append_read (stream cursor value n : Nat) (used : stream < 2^cursor)
    (byteField : n ≤ 64) (fits : value < 2^n) :
    get (append stream cursor value) cursor n = value ∧
    (append stream cursor value) % 2^cursor = stream ∧
    append stream cursor value < 2^(cursor+n) := by
  unfold append
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt used, Nat.shiftLeft_eq]
  have sum : value * 2^cursor + stream = stream + value * 2^cursor := Nat.add_comm _ _
  rw [sum]
  have pos := Nat.two_pow_pos cursor
  refine ⟨?_, ?_, ?_⟩
  · rw [get_eq _ _ _ byteField, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ pos,
      Nat.div_eq_of_lt used, Nat.zero_add, Nat.mod_eq_of_lt fits]
  · simp [Nat.mod_eq_of_lt used]
  · have mul := Nat.mul_le_mul_right (2^cursor) (Nat.succ_le_of_lt fits)
    rw [Nat.succ_mul] at mul
    rw [Nat.pow_add, Nat.mul_comm (2^cursor) (2^n)]
    omega

private theorem beyond (x w i : Nat) (bound : x < 2^w) (idx : w ≤ i) :
    x.testBit i = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) idx))

/-- First word written by the opener, including a field ending in the next word. -/
theorem put_first (stream cursor value : Nat) :
    word (append stream cursor value) (cursor/64) =
      word stream (cursor/64) ||| ((value <<< (cursor%64)) % 2^64) := by
  apply Nat.eq_of_testBit_eq
  intro b
  have off := Nat.div_add_mod cursor 64
  by_cases inside : b < 64
  · have le : 64*(cursor/64)+b ≥ cursor ↔ b ≥ cursor%64 := by omega
    have sub : 64*(cursor/64)+b-cursor = b-cursor%64 := by omega
    simp only [bit_word, append, Nat.testBit_or, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftLeft, inside, decide_true, Bool.true_and, le, sub]
  · simp only [bit_word, Nat.testBit_or, Nat.testBit_mod_two_pow, inside, decide_false,
      Bool.false_and, Bool.false_or]

theorem empty_word_at_boundary (stream cursor : Nat) (used : stream < 2^cursor)
    (aligned : cursor % 64 = 0) : word stream (cursor/64) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  have off := Nat.div_add_mod cursor 64
  have z := beyond stream cursor (64*(cursor/64)+b) used (by omega)
  simp [bit_word,z]

/-- The overflow word is the high portion of the field. If the field ends at or
before the current word boundary, this expression is zero. -/
theorem put_next (stream cursor value : Nat) (used : stream < 2^cursor) :
    word (append stream cursor value) (cursor/64+1) =
      (value >>> (64-cursor%64)) % 2^64 := by
  apply Nat.eq_of_testBit_eq
  intro b
  have off := Nat.div_add_mod cursor 64
  have rem := Nat.mod_lt cursor (by decide : 0 < 64)
  have ge : 64*(cursor/64+1)+b ≥ cursor := by omega
  have sub : 64*(cursor/64+1)+b-cursor = 64-cursor%64+b := by omega
  have z := beyond stream cursor (64*(cursor/64+1)+b) used ge
  simp only [bit_word, append, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, z, ge, decide_true, Bool.false_or, Bool.true_and, sub]

theorem no_overflow (value cursor n : Nat) (fits : value < 2^n) (ends : cursor%64+n ≤ 64) :
    (value >>> (64-cursor%64)) % 2^64 = 0 := by
  have small := Nat.lt_of_lt_of_le fits (Nat.pow_le_pow_right (by decide) (show n ≤ 64-cursor%64 by omega))
  simp [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt small]

theorem put_frame (stream value cursor n j : Nat) (fits : value < 2^n) (width : n ≤ 64)
    (outside : j < cursor/64 ∨ cursor/64+1 < j) :
    word (append stream cursor value) j = word stream j := by
  have off := Nat.div_add_mod cursor 64
  have rem := Nat.mod_lt cursor (by decide : 0 < 64)
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases inside : b < 64
  · rcases outside with before | after
    · have early : ¬ 64*j+b ≥ cursor := by omega
      simp [bit_word, append, Nat.testBit_shiftLeft, inside, early]
    · have late : n ≤ 64*j+b-cursor := by omega
      have z := beyond _ _ _ fits late
      simp [bit_word, append, Nat.testBit_shiftLeft, inside, z]
  · simp [bit_word, inside]

end CommitGolfCandidate.Reconstruction.HonestStream
