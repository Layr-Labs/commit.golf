import CommitGolfCandidate.K1Manifest
import CommitGolfCandidate.ProjectedHalfwordMemory
import RiscvZkvm.Rv64.Logic.ByteOps
namespace CommitGolfCandidate.Layout2Helpers
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
theorem offset_nat (q : Nat) (fit : q < 2^64) : byteOffset (BitVec.ofNat 64 q) = q % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit,
    show (7#64 : Word).toNat = 2^3-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem align_nat (q : Nat) (fit : q < 2^64) : (alignToDword (BitVec.ofNat 64 q)).toNat = q - q % 8 := by
  let word : Word := BitVec.ofNat 64 q
  let aligned := alignToDword word
  have wordAsNat : word.toNat = q := by
    simp only [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : q < 2^64)]
  have alignedAtMost : aligned.toNat ≤ q := by
    rw [show aligned.toNat = word.toNat &&& (~~~7#64).toNat by exact BitVec.toNat_and _ _]
    exact Nat.and_le_left.trans (le_of_eq wordAsNat)
  have offset : byteOffset word = q % 8 := offset_nat q (by omega)
  have whole := congrArg BitVec.toNat (alignToDword_add_byteOffset word)
  change (aligned+BitVec.ofNat 64 (byteOffset word)).toNat = word.toNat at whole
  rw [BitVec.toNat_add, wordAsNat, BitVec.toNat_ofNat, offset, Nat.mod_eq_of_lt (by omega : q % 8 < 2^64),
    Nat.mod_eq_of_lt (by omega)] at whole
  change aligned.toNat = _
  omega

theorem align_eq (q : Nat) (fit : q < 2^64) :
    alignToDword (BitVec.ofNat 64 q) = BitVec.ofNat 64 (q - q % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [align_nat q fit, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem byte_at (s : MachineState) (base i : Nat) (aligned : base % 8 = 0) (small : i < 8) (fit : base+8 ≤ 2^64) :
    s.getByte (BitVec.ofNat 64 (base+i)) = extractByte (s.getMem (BitVec.ofNat 64 base)) i := by
  unfold MachineState.getByte
  rw [align_eq (base+i) (by omega), offset_nat (base+i) (by omega),
    show base+i - (base+i)%8 = base by omega, show (base+i)%8 = i by omega]

theorem access_ok (a w : Nat) (aligned : a % w = 0) (fit : a+w ≤ MEMORY_BYTES) :
    accessValid (BitVec.ofNat 64 a) w = true := by
  have small : a < 2^64 := by unfold MEMORY_BYTES at fit; omega
  unfold accessValid rangeValid
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  simp only [aligned, decide_true, Bool.and_true, decide_eq_true_eq]
  exact fit

theorem same_dword (a b : Nat) (fa : a+8 ≤ 2^64) (fb : b+8 ≤ 2^64) (same : a - a % 8 = b - b % 8) :
    alignToDword (BitVec.ofNat 64 a) = alignToDword (BitVec.ofNat 64 b) :=
  BitVec.eq_of_toNat_eq (by rw [align_nat a (by omega), align_nat b (by omega)]; exact same)

theorem extract_shift (x : BitVec 16) (k : Nat) : x.extractLsb' k 8 = (x >>> k).truncate 8 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, BitVec.truncate, BitVec.toNat_setWidth]

theorem half_ext (x y : BitVec 16) (low : x.extractLsb' 0 8 = y.extractLsb' 0 8)
    (high : x.extractLsb' 8 8 = y.extractLsb' 8 8) : x = y := by
  apply BitVec.eq_of_toNat_eq
  have l := congrArg BitVec.toNat low
  have h := congrArg BitVec.toNat high
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at l h
  have hx : x.toNat < 65536 := x.isLt
  have hy : y.toNat < 65536 := y.isLt
  norm_num at l h
  omega

theorem halfword_bytes (s : MachineState) (a : Nat) (even : a % 2 = 0) (fit : a+16 ≤ 2^64) :
    (s.getHalfword (BitVec.ofNat 64 a)).extractLsb' 0 8 = s.getByte (BitVec.ofNat 64 a) ∧
    (s.getHalfword (BitVec.ofNat 64 a)).extractLsb' 8 8 = s.getByte (BitVec.ofNat 64 (a+1)) := by
  have oa := offset_nat a (by omega)
  have ob := offset_nat (a+1) (by omega)
  constructor
  · have low := ProjectedHalfword.load_byte s (BitVec.ofNat 64 a) (BitVec.ofNat 64 a) rfl rfl
    rw [oa, show a % 8 % 2 = 0 by omega, Nat.zero_mul] at low
    rw [extract_shift]
    exact low
  · have high := ProjectedHalfword.load_byte s (BitVec.ofNat 64 a) (BitVec.ofNat 64 (a+1))
      (same_dword _ _ (by omega) (by omega) (by omega)) (by rw [oa, ob]; omega)
    rw [ob, show (a+1) % 8 % 2 = 1 by omega, Nat.one_mul] at high
    rw [extract_shift]
    exact high

theorem halfword_of_bytes (s t : MachineState) (a : Nat) (even : a % 2 = 0) (fit : a+16 ≤ 2^64)
    (low : t.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a))
    (high : t.getByte (BitVec.ofNat 64 (a+1)) = s.getByte (BitVec.ofNat 64 (a+1))) :
    t.getHalfword (BitVec.ofNat 64 a) = s.getHalfword (BitVec.ofNat 64 a) := by
  have hs := halfword_bytes s a even fit
  have ht := halfword_bytes t a even fit
  exact half_ext _ _ (by rw [ht.1, hs.1, low]) (by rw [ht.2, hs.2, high])

def pget : {n : Nat} → ArtifactEncoding.Packed n → Nat → Nat
  | _, .chunk _ payload, k => (payload >>> (8*k)) % 256
  | _, @ArtifactEncoding.Packed.join l _ left right, k => if k < l then pget left k else pget right (k-l)

theorem pget_get : ∀ {n : Nat} (packed : ArtifactEncoding.Packed n) (k : Fin n),
    (packed.get 8 k).toNat = pget packed k.val
  | _, .chunk _ payload, k => by
    simp [ArtifactEncoding.Packed.get, pget, BitVec.toNat_ofNat]
  | _, @ArtifactEncoding.Packed.join l r left right, k => by
    by_cases h : k.val < l
    · rw [ArtifactEncoding.get_join_left 8 left right k h, pget_get left]
      simp [pget, h]
    · rw [ArtifactEncoding.get_join_right 8 left right k h, pget_get right]
      simp [pget, h]

end CommitGolfCandidate.Layout2Helpers
