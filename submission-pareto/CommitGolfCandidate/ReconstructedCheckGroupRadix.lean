import CommitGolfCandidate.ReconstructedOpeningHorner
import CommitGolfCandidate.ReconstructedCapDigits
import CommitGolfCandidate.ReconstructedCheckCapSlots

namespace CommitGolfCandidate.Reconstruction.CheckGroupRadix
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 12000
set_option maxHeartbeats 1100000
abbrev W := BitVec.ofNat 64
abbrev magic : Nat := 5595220951267352149
abbrev cap : Nat := 4194304
def top (id : Nat) := cap/8+4*id+3
def fix (mem : Memory) (id digit : Nat) := writeWord mem (top id) (mem (top id) ||| (W digit <<< (32 : Nat)))

theorem shift (n k : Nat) : W n <<< k = W (n*2^k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,Nat.mod_mul_mod]

theorem clip (w : Word) : ((w <<< (33 : Nat)) >>> (33 : Nat))=W (w.toNat%2^31) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,Nat.shiftRight_eq_div_pow,Nat.shiftLeft_eq,
    show 2^64=2^31*2^33 by decide,Nat.mul_mod_mul_right,Nat.mul_div_cancel _ (by decide : 0<2^33)]
  simp only [BitVec.toNat_ofNat]
  omega

theorem quotient (n : Nat) (small : n<2^31) :
    (rv64_mulhu (W n) (W magic)) >>> (6 : Nat) = W (n/211) := by
  rw [OpeningHorner.upper_product]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  change (((n%2^64)*5595220951267352149/2^64)%2^64)/64=(n/211)%2^64
  have rem := Nat.mod_lt n (by decide : 0<211)
  have split := Nat.div_add_mod n 211
  have decomp : n*5595220951267352149=(15*(n/211)+(n%211)*5595220951267352149)+2^70*(n/211) := by
    calc n*5595220951267352149=(211*(n/211)+n%211)*5595220951267352149 := congrArg (·*5595220951267352149) split.symm
         _=_ := by ring
  rw [Nat.mod_eq_of_lt (by omega : n<2^64),Nat.mod_eq_of_lt (by omega : n*5595220951267352149/2^64<2^64),
    Nat.mod_eq_of_lt (by omega : n/211<2^64),Nat.div_div_eq_div_mul,show 2^64*64=2^70 by decide,decomp,
    Nat.add_mul_div_left _ _ (by decide : 0<2^70),Nat.div_eq_of_lt (by omega : 15*(n/211)+(n%211)*5595220951267352149<2^70),
    Nat.zero_add]

private theorem subShift (a b : Word) :
    ((a.truncate 32-b.truncate 32).signExtend 64 <<< (32 : Nat)) = ((a-b) <<< (32 : Nat)) := by bv_decide

theorem high (n : Nat) :
    (((W n).truncate 32-((W (n/211))*(W 211)).truncate 32).signExtend 64) <<< (32 : Nat) =
      W (n%211) <<< (32 : Nat) := by
  have dec : W n=W (n%211)+W (n/211*211) := by rw [←BitVec.ofNat_add];congr 1;omega
  rw [subShift,←BitVec.ofNat_mul,dec,BitVec.add_sub_cancel]

theorem idAddress (id : Nat) : (W id <<< (5 : Nat))+W cap+signExtend12 24=wordAddress (top id) := by
  rw [shift,←BitVec.ofNat_add,show signExtend12 24=W 24 by decide,←BitVec.ofNat_add]
  change W (id*32+4194304+24)=W (8*(524288+4*id+3))
  congr 1;omega

theorem index (n : Nat) (small : n<2^32) : ((W n <<< (32 : Nat)) >>> (30 : Nat))=W (4*n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight,BitVec.toNat_shiftLeft,BitVec.toNat_ofNat,Nat.shiftLeft_eq,Nat.shiftRight_eq_div_pow]
  omega

end CommitGolfCandidate.Reconstruction.CheckGroupRadix

