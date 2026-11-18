import CommitGolf.Riscv

/-! Word-level facts for 244-bit leaf digests: a digest cut to its low 244 bits
keeps its three low doublewords and the low 52 bits of the top one. Commit masks
with `and` by `2^52-1`; the checker uses `slli 12; srli 12`. -/
namespace TwoPermutationPrototype
open RiscvZkvm.Rv64

/-- The kept low 52 bits of a leaf digest's top doubleword (digest bits 192..243). -/
def leafMask : Word := BitVec.ofNat 64 (2^52-1)

private theorem mask_bit (k : Nat) : leafMask.getLsbD k = decide (k < 52 ∧ k < 64) := by
  unfold leafMask
  rw [BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases h : k < 52 <;> by_cases h' : k < 64 <;> simp [h, h'] <;> omega

theorem trunc_top_word (d : BitVec 256) :
    (BitVec.ofNat 256 (d.toNat % 2^244)).extractLsb' 192 64 = d.extractLsb' 192 64 &&& leafMask := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_and, mask_bit, BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow, BitVec.testBit_toNat]
  by_cases h : k < 52
  · simp [h, hk, show 192+k < 244 by omega, show 192+k < 256 by omega]
  · simp [h, show ¬ 192+k < 244 by omega]

theorem trunc_low_word (d : BitVec 256) (k : Nat) (hk : k < 3) :
    (BitVec.ofNat 256 (d.toNat % 2^244)).extractLsb' (64*k) 64 = d.extractLsb' (64*k) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofNat, Nat.testBit_mod_two_pow,
    BitVec.testBit_toNat]
  simp [hi, show 64*k+i < 244 by omega, show 64*k+i < 256 by omega]

/-- `slli 12; srli 12` keeps the low 52 bits. -/
theorem shift_mask (x : Word) : (x <<< (12 : Nat)) >>> (12 : Nat) = x &&& leafMask := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_and, leafMask, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : (2:Nat)^52-1 < 2^64), Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    show (2:Nat)^64 = 2^52*2^12 by norm_num, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (by norm_num)]

end TwoPermutationPrototype
