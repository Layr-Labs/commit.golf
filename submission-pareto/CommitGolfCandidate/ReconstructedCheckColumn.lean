import CommitGolfCandidate.ReconstructedCheckDivision

namespace CommitGolfCandidate.Reconstruction.CheckColumn
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 CommitGolfCandidate
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000

abbrev W := BitVec.ofNat 64
abbrev limb := 2^32

private theorem w_mul (a c : Nat) : BitVec.ofNat 64 a * BitVec.ofNat 64 c = BitVec.ofNat 64 (a * c) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mul_mod]
private theorem w_sub (a c : Nat) (h : c ≤ a) (ha : a < 2^64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 c = BitVec.ofNat 64 (a - c) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
private theorem w_divu (a c : Nat) (hc : 0 < c) (ha : a < 2^64) (hc' : c < 2^64) :
    rv64_divu (BitVec.ofNat 64 a) (BitVec.ofNat 64 c) = BitVec.ofNat 64 (a / c) := by
  have nonzero : BitVec.ofNat 64 c≠0#64 := by
    intro h;have v:=congrArg BitVec.toNat h;change c%2^64=0 at v;omega
  have test : ¬(BitVec.ofNat 64 c == 0#64)=true := fun h=>nonzero (beq_iff_eq.1 h)
  rw [rv64_divu,ite_eq_right test]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_udiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hc',
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

private theorem w_shl (a c : Nat) : BitVec.ofNat 64 a <<< c = BitVec.ofNat 64 (a * 2^c) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.shiftLeft_eq, Nat.mul_mod]
private theorem w_shr (a c : Nat) (ha : a < 2^64) : BitVec.ofNat 64 a >>> c = BitVec.ofNat 64 (a / 2^c) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : a % 18446744073709551616 = a := Nat.mod_eq_of_lt ha
  have h2 : a / 2 ^ c % 18446744073709551616 = a / 2 ^ c :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) ha)
  simp [Nat.shiftRight_eq_div_pow, h1, h2]
private theorem w_or_mul (a c p : Nat) (s : Nat) (hp : p = 2^s) (ha : a < p) (h1 : a < 2^64) (h2 : c * p < 2^64)
    (h3 : a + c * p < 2^64) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 (c * p) = BitVec.ofNat 64 (a + c * p) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1,Nat.mod_eq_of_lt h2,Nat.mod_eq_of_lt h3]
  subst hp
  rw [Nat.add_comm, Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt ha, Nat.or_comm]

theorem joined (rem x : Nat) (rh : rem<limb) (xh : x<limb) :
    (W rem <<< (32 : Nat)) ||| W x=W (rem*limb+x) := by
  unfold limb at *
  rw [w_shl,BitVec.or_comm,w_or_mul x rem (2^32) 32 rfl xh (by omega) (by omega) (by omega),Nat.add_comm]

private theorem signed_rem (x product rem carry : Nat) (small : x<limb) (carryWord : carry<limb)
    (short : rem<2^31) (equation : carry*limb+x=product+rem) :
    (((W x).truncate 32-(W product).truncate 32).signExtend 64)=W rem := by
  unfold limb at *
  let v := (W x).truncate 32-(W product).truncate 32
  have left : v.toNat=rem := by
    simp only [v,BitVec.toNat_sub,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  have sign : v.msb=false := by rw [BitVec.msb_eq_decide,left];exact decide_eq_false (by omega)
  change v.signExtend 64=_
  rw [BitVec.signExtend_eq_setWidth_of_msb_false sign]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,BitVec.toNat_ofNat,left]

def quotient (part base : Word) := (rv64_divu part base <<< (32 : Nat)) >>> (32 : Nat)
def carryWord (low part base : Word) :=
  (low.truncate 32 - ((rv64_divu part base*base).truncate 32)).signExtend 64

private theorem clip (x : Nat) (small : x<2^32) : (W x <<< (32 : Nat)) >>> (32 : Nat) = W x := by
  rw [w_shl,w_shr (x*2^32) 32 (by omega)]
  exact congrArg W (Nat.mul_div_cancel x (by decide))

theorem column (carry x base : Nat) (range : 0<base ∧ base≤2^31) (carryBound : carry<base) (xBound : x<limb) :
    let part:=carry*limb+x
    quotient (W part) (W base)=W (part/base) ∧ carryWord (W x) (W part) (W base)=W (part%base) ∧
      part/base<limb ∧ part%base<base := by
  unfold limb at *
  let part:=carry*2^32+x
  have lt : part<base*2^32 := by dsimp [part];omega
  have small : part<2^64 := by omega
  have prod : part/base*base≤part := Nat.div_mul_le_self _ _
  have rb : part%base<base:=Nat.mod_lt _ range.1
  have qb : part/base<2^32 := (Nat.div_lt_iff_lt_mul range.1).2 (by rw [Nat.mul_comm];exact lt)
  have eq : carry*2^32+x=part/base*base+part%base := by rw [Nat.mul_comm (part/base) base];exact (Nat.div_add_mod part base).symm
  refine ⟨?_,?_,qb,rb⟩
  · change quotient (W part) (W base)=_
    rw [quotient,w_divu _ _ range.1 small (by omega),clip _ qb]
  · change carryWord (W x) (W part) (W base)=_
    rw [carryWord,w_divu _ _ range.1 small (by omega),w_mul]
    exact signed_rem x (part/base*base) (part%base) carry xBound (by unfold limb;omega) (by omega) eq

theorem last_rem (carry x base : Nat) (range : 0<base ∧ base≤2^31) (carryBound : carry<base) (xBound : x<limb) :
    let part:=carry*limb+x
    W part - (rv64_divu (W part) (W base)*W base)=W (part%base) := by
  unfold limb at *
  let part:=carry*2^32+x
  have small : part<2^64 := by dsimp [part];omega
  change W part-(_*W base)=W (part%base)
  rw [w_divu _ _ range.1 small (by omega),w_mul,w_sub _ _ (Nat.div_mul_le_self _ _) small]
  have eq:=Nat.div_add_mod part base;rw [Nat.mul_comm base (part/base)] at eq
  exact congrArg W (by omega)

end CommitGolfCandidate.Reconstruction.CheckColumn
