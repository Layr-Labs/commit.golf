import CommitGolfCandidate.Padding96Memory

/-! Range checks sufficient for the adapter's word accesses and temporary padding. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem padding_source_words (source : Word)
    (valid : rangeValid source 96 = true) (aligned : source.toNat % 8 = 0) :
    ∀ word : Fin 4, accessValid (source+BitVec.ofNat 64 (64+8*word.val)) 8 = true := by
  intro word
  have inside := word.isLt
  simp only [rangeValid, decide_eq_true_eq] at valid
  have offsetBound : 64+8*word.val < 2^64 := by omega
  have sumBound : source.toNat+(64+8*word.val) < 2^64 := by
    unfold MEMORY_BYTES at valid
    omega
  simp only [accessValid, rangeValid, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt offsetBound, Nat.mod_eq_of_lt sumBound, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor <;> omega

/-- All output words precede the temporary padding in the baseline's calls. -/
theorem padding_output_separate (source destination : Word)
    (sourceValid : rangeValid source 96 = true)
    (destinationValid : rangeValid destination 32 = true)
    (before : destination.toNat+32 ≤ source.toNat+64) :
    ∀ word < 4, ∀ byte < 32,
      source+BitVec.ofNat 64 (64+8*word) ≠
        alignToDword (destination+BitVec.ofNat 64 byte) := by
  intro word wordBound byte byteBound equal
  simp only [rangeValid, decide_eq_true_eq] at sourceValid destinationValid
  have sourceSum : source.toNat+(64+8*word) < 2^64 := by
    unfold MEMORY_BYTES at sourceValid
    omega
  have destinationSum : destination.toNat+byte < 2^64 := by
    unfold MEMORY_BYTES at destinationValid
    omega
  have alignedLe : (alignToDword (destination+BitVec.ofNat 64 byte)).toNat ≤
      (destination+BitVec.ofNat 64 byte).toNat := by
    unfold alignToDword
    rw [BitVec.toNat_and]
    exact Nat.and_le_left
  have natural := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 64+8*word < 2^64),
    Nat.mod_eq_of_lt (by omega : byte < 2^64),
    Nat.mod_eq_of_lt sourceSum, Nat.mod_eq_of_lt destinationSum] at natural alignedLe
  omega

end CommitGolfCandidate
