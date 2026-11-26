import CommitGolfCandidate.ReconstructedOpeningLinear

namespace CommitGolfCandidate.Reconstruction.OpeningHorner
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OpeningCursor
set_option maxRecDepth 10000

abbrev modulus : Nat := 2^64

theorem upper_product (a b : Word) : rv64_mulhu a b = W (a.toNat*b.toNat/modulus) := by
  have fit : a.toNat*b.toNat<2^128 := BitVec.toNat_mul_toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp only [rv64_mulhu,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,BitVec.toNat_mul,W,BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by have := a.isLt;omega : a.toNat<2^128),
    Nat.mod_eq_of_lt (by have := b.isLt;omega : b.toNat<2^128),Nat.mod_eq_of_lt fit,Nat.shiftRight_eq_div_pow]

def carry (new product : Word) : Word := if new.ult product then 1 else 0

theorem low (v b d : Nat) : W v*W b+W d=W (v*b+d) := by
  simp only [W,BitVec.ofNat_add,BitVec.ofNat_mul]

private theorem digit_carry (p d : Nat) (small : d<modulus) :
    W (p/modulus)+carry (W (p+d)) (W p)=W ((p+d)/modulus) := by
  unfold modulus at *
  unfold carry
  simp only [BitVec.ult_eq_decide,decide_eq_true_eq,BitVec.toNat_ofNat]
  split
  · rename_i h
    change W (p/2^64)+W 1=W ((p+d)/2^64)
    rw [←BitVec.ofNat_add];congr 1;omega
  · rename_i h
    change W (p/2^64)+W 0=W ((p+d)/2^64)
    rw [←BitVec.ofNat_add];congr 1;omega

/-- The low-product overflow and the independent addition carry reconstruct the
high word even when the low 64-bit product wraps. -/
theorem high (v b d : Nat) (radix : b<modulus) (digit : d<modulus) :
    (W (v/modulus)*W b+rv64_mulhu (W v) (W b))+
      carry (W (v*b+d)) (W (v*b)) = W ((v*b+d)/modulus) := by
  let p := (v%modulus)*b
  have expand : v*b+d=(p+d)+modulus*((v/modulus)*b) := by
    have h := congrArg (fun t => t*b) (Nat.div_add_mod v modulus)
    change (modulus*(v/modulus)+v%modulus)*b=v*b at h
    rw [Nat.add_mul,Nat.mul_assoc] at h
    unfold p;omega
  have congrLow : W (v*b)=W p := by
    apply BitVec.eq_of_toNat_eq
    exact (Nat.mod_mul_mod v b modulus).symm
  have congrSum : W (v*b+d)=W (p+d) := (BitVec.ofNat_add ..).trans ((congrArg (· + W d) congrLow).trans (BitVec.ofNat_add ..).symm)
  rw [congrLow,congrSum,upper_product,show (W v).toNat=v%modulus by rfl,show (W b).toNat=b from Nat.mod_eq_of_lt radix]
  change (W (v/modulus)*W b+W (p/modulus))+carry (W (p+d)) (W p)=_
  rw [BitVec.add_assoc,digit_carry p d digit,←BitVec.ofNat_mul,←BitVec.ofNat_add,expand,
    Nat.add_mul_div_left _ _ (by decide : 0<modulus),Nat.add_comm]

end CommitGolfCandidate.Reconstruction.OpeningHorner
