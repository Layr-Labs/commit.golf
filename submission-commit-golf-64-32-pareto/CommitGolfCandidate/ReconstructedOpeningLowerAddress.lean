import CommitGolfCandidate.ReconstructedOpeningHeaderAddress

namespace CommitGolfCandidate.Reconstruction.OpeningLowerAddress
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OpeningCursor OpeningHeaderAddress Encoding
set_option maxRecDepth 12000

theorem last (i : Index) :
    ((W (2^24+i.val) ^^^ signExtend12 1) <<< (5 : Nat))+W heap=basePtr i 24 := by
  change ((W (2^24+i.val) ^^^ W 1) <<< (5 : Nat))+W heap=_
  rw [←BitVec.ofNat_xor,BitVec.shiftLeft_eq_mul_twoPow]
  change W ((2^24+i.val) ^^^ 1)*W 32+W heap=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add]
  unfold basePtr sibling
  simp only [show 24-24=0 from rfl,Nat.shiftRight_zero,Nat.add_comm _ heap,Nat.mul_comm _ 32]

theorem previous (i : Index) (d : Nat) (lo : 20≤d) (hi : d≤23) :
    ((((W (2^24+i.val) <<< (d-19)) &&& signExtend12 4064) ^^^ signExtend12 32)+W heap=basePtr i d) := by
  let n := 2^24+i.val
  have ns : n<2^25 := by have := i.isLt;change i.val<2^24 at this;dsimp [n];omega
  have shift (s : Nat) : W n <<< s = W (n*2^s) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft,W,BitVec.toNat_ofNat,Nat.shiftLeft_eq,Nat.mod_eq_of_lt (by omega : n<2^64)]
  have sh := shift (d-19)
  change (((W n <<< (d-19)) &&& _) ^^^ _)+_=_
  rw [sh]
  have fit : n*2^(d-19)<2^64 := by interval_cases d <;> omega
  have h := compiled (n*2^(d-19)) 0 fit
  rw [BitVec.ushiftRight_zero] at h
  rw [h,←BitVec.ofNat_add]
  unfold basePtr sibling
  have div : (n*2^(d-19)) >>> (0+5)=(2^24+i.val) >>> (24-d) := by
    change (n*2^(d-19)) >>> 5=n >>> (24-d)
    simp only [Nat.shiftRight_eq_div_pow];interval_cases d <;> omega
  rw [div,Nat.add_comm]
end CommitGolfCandidate.Reconstruction.OpeningLowerAddress
