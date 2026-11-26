import CommitGolfCandidate.S4Slots
import CommitGolfCandidate.S4ByteFrame
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (saltAddress rowBase rowAddress levelOffset)

theorem shifted (n k : Nat) : W n <<< k=W (n*2^k) := by
  apply BitVec.eq_of_toNat_eq;simp [W,BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.mul_mod]
theorem shr (n k : Nat) (small : n<2^64) : W n >>> k=W (n/2^k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [W,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt small,
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self ..) small)]
theorem parity (n : Nat) : W n &&& 1 = W (n%2) := by
  change BitVec.ofNat 64 n &&& BitVec.ofNat 64 (2^1-1)=_
  rw [←BitVec.ofNat_and,Nat.and_two_pow_sub_one_eq_mod]
theorem flip (n : Nat) : (W n &&& 1) ^^^ 1=W (1-n%2) := by
  rw [parity];rcases (show n%2=0 ∨ n%2=1 by omega) with e|e <;> rw [e] <;> rfl
theorem divThree (n : Nat) (small : n<2^64) : rv64_divu (W n) 3=W (n/3) := by
  change W n/(3 : Word)=_;apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  change n/3=n/3%2^64;exact (Nat.mod_eq_of_lt (by omega)).symm
theorem modThree (n : Nat) (small : n<2^64) : rv64_remu (W n) 3=W (n%3) := by
  change W n%(3 : Word)=_;apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  change n%3=n%3%2^64;exact (Nat.mod_eq_of_lt (by omega)).symm

theorem rowAddrCalc (base j : Nat) : (((W j <<< 1)+W j) <<< 5)+W base=W (base+96*j) := by
  rw [shifted];change (BitVec.ofNat 64 (j*2)+BitVec.ofNat 64 j) <<< 5+_=_
  rw [←BitVec.ofNat_add,shifted];exact (BitVec.ofNat_add ..).symm.trans (congrArg W (by omega))

theorem saltPtr (i : Index) :
    W rowBase + (((W i.val <<< 1) + W i.val) <<< 5) + (((W i.val &&& 1) + 18446744073709551615) &&& 72) =
    W (saltAddress i) := by
  simp only [W] at *
  have p : BitVec.ofNat 64 i.val &&& 1 = BitVec.ofNat 64 (i.val%2):=parity i.val
  rw [p,shifted,←BitVec.ofNat_add,shifted,←BitVec.ofNat_add]
  by_cases e : i.val%2=0
  · rw [e];change BitVec.ofNat 64 _ + BitVec.ofNat 64 72 = _
    rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64); unfold saltAddress;rw [if_pos e];omega
  · rw [show i.val%2=1 by omega];change BitVec.ofNat 64 _ + BitVec.ofNat 64 0 = _
    rw [←BitVec.ofNat_add];apply congrArg (BitVec.ofNat 64); unfold saltAddress;rw [if_neg e];omega

theorem slotPick (left right : Bool) (a b : Word) :
    a ^^^ ((a ^^^ b) &&& (((if left then 1 else 0 : Word) ||| (if right then 1 else 0)) - 1)) =
      if left || right then a else b := by
  cases left <;> cases right <;> simp [BitVec.sub_eq_add_neg]
  change a ^^^ ((a ^^^ b) &&& BitVec.allOnes 64)=b
  rw [BitVec.and_allOnes,←BitVec.xor_assoc,BitVec.xor_self,BitVec.zero_xor]

theorem oneMore (a : Nat) : W a+1=W (a+1):=(BitVec.ofNat_add ..).symm
theorem prev (n : Nat) (pos : 0<n) : W n+18446744073709551615=W (n-1) := by
  change BitVec.ofNat 64 n+(-1)=_;rw [←BitVec.sub_eq_add_neg];exact BitVec.ofNat_sub_ofNat_of_le _ 1 (by decide) pos
end CommitGolfCandidate.S4.Machine
