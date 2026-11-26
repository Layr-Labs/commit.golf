import CommitGolfCandidate.InputMemory
import CommitGolfCandidate.Model

/-! Memory facts for the 24-byte salts: a salt is three consecutive words, and a leaf
state written as three salt words followed by a zero word is `saltState` of the salt. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

private theorem salt_append_nat {highWidth lowWidth : Nat}
    (high : BitVec highWidth) (low : BitVec lowWidth) :
    (high ++ low).toNat = high.toNat * 2^lowWidth + low.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt, Nat.shiftLeft_eq]

/-- A 24-byte read concatenates three consecutive words, low word first in memory. -/
theorem read_salt_words (state : MachineState) (address : Nat) (aligned : address % 8 = 0) :
    readBuffer state address 24 =
      (state.getMem (BitVec.ofNat 64 (address + 16)) ++
        state.getMem (BitVec.ofNat 64 (address + 8))) ++
        state.getMem (BitVec.ofNat 64 address) := by
  have slice := read_buffer_slice state address 32 0 24 (by decide)
  simp only [Nat.add_zero, Nat.mul_zero] at slice
  rw [← slice, read_digest_words _ _ aligned]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, salt_append_nat, Nat.shiftRight_zero]
  have b0 := (state.getMem (BitVec.ofNat 64 address)).isLt
  have b1 := (state.getMem (BitVec.ofNat 64 (address + 8))).isLt
  have b2 := (state.getMem (BitVec.ofNat 64 (address + 16))).isLt
  have b3 := (state.getMem (BitVec.ofNat 64 (address + 24))).isLt
  generalize (state.getMem (BitVec.ofNat 64 address)).toNat = w0 at *
  generalize (state.getMem (BitVec.ofNat 64 (address + 8))).toNat = w1 at *
  generalize (state.getMem (BitVec.ofNat 64 (address + 16))).toNat = w2 at *
  generalize (state.getMem (BitVec.ofNat 64 (address + 24))).toNat = w3 at *
  norm_num at b0 b1 b2 b3 ⊢
  omega

/-- Salt equality from the three word equalities (the fourth word is irrelevant). -/
theorem read_salt_congr (left right : MachineState) (leftAddress rightAddress : Nat)
    (leftAligned : leftAddress % 8 = 0) (rightAligned : rightAddress % 8 = 0)
    (words : ∀ word < 3, left.getMem (BitVec.ofNat 64 (leftAddress+8*word)) =
      right.getMem (BitVec.ofNat 64 (rightAddress+8*word))) :
    readBuffer left leftAddress 24 = readBuffer right rightAddress 24 := by
  rw [read_salt_words _ _ leftAligned, read_salt_words _ _ rightAligned]
  have w0 := words 0 (by decide)
  have w1 := words 1 (by decide)
  have w2 := words 2 (by decide)
  simp only [Nat.reduceMul, Nat.add_zero] at w0 w1 w2
  rw [w0, w1, w2]

/-- Extracting one word of a loaded salt recovers the corresponding memory word. -/
theorem read_salt_word (state : MachineState) (address word : Nat)
    (aligned : address % 8 = 0) (bounded : word < 3) :
    (readBuffer state address 24).extractLsb' (64*word) 64 =
      state.getMem (BitVec.ofNat 64 (address+8*word)) := by
  rw [read_salt_words _ _ aligned]
  interval_cases word
  · exact BitVec.extractLsb'_append_eq_right
  · exact (BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 64)).trans
      BitVec.extractLsb'_append_eq_right
  · exact (BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 128)).trans
      BitVec.extractLsb'_append_eq_left

/-- The salt equals the source salt iff the three words match. -/
theorem read_salt_eq_iff (left right : MachineState) (leftAddress rightAddress : Nat)
    (leftAligned : leftAddress % 8 = 0) (rightAligned : rightAddress % 8 = 0) :
    readBuffer left leftAddress 24 = readBuffer right rightAddress 24 ↔
      ∀ word < 3, left.getMem (BitVec.ofNat 64 (leftAddress+8*word)) =
        right.getMem (BitVec.ofNat 64 (rightAddress+8*word)) := by
  constructor
  · intro equal word bounded
    have extracted := congrArg (fun salt : BitVec 192 => salt.extractLsb' (64*word) 64) equal
    simpa only [read_salt_word _ _ _ leftAligned bounded,
      read_salt_word _ _ _ rightAligned bounded] using extracted
  · exact read_salt_congr left right leftAddress rightAddress leftAligned rightAligned

/-- A 32-byte leaf state whose high word is zero is `saltState` of its low 24 bytes. -/
theorem read_salt_state (state : MachineState) (address : Nat) (aligned : address % 8 = 0)
    (zero : state.getMem (BitVec.ofNat 64 (address + 24)) = 0) :
    readBuffer state address 32 = saltState (readBuffer state address 24) := by
  rw [read_digest_words _ _ aligned, read_salt_words _ _ aligned, zero, saltState]
  apply BitVec.eq_of_toNat_eq
  simp only [salt_append_nat]
  ring

end CommitGolfCandidate
