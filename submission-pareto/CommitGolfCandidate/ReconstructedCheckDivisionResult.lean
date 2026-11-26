import CommitGolfCandidate.ReconstructedCheckColumn

namespace CommitGolfCandidate.Reconstruction.CheckDivisionResult
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 LeafModel CheckColumn CheckDivision
set_option maxRecDepth 20000
set_option maxHeartbeats 1800000

def p2 (m : Model) (b : Word) :=
  (carryWord (m.reg .x27) (m.reg .x27) b <<< (32 : Nat)) ||| m.reg .x18
def p1 (m : Model) (b : Word) :=
  (carryWord (m.reg .x18) (p2 m b) b <<< (32 : Nat)) ||| m.reg .x20
def p0 (m : Model) (b : Word) :=
  (carryWord (m.reg .x20) (p1 m b) b <<< (32 : Nat)) ||| m.reg .x25
def rem (m : Model) (b : Word) := p0 m b - (rv64_divu (p0 m b) b*b)

private theorem shape (m : Model) (cell : Nat) :
    let b:=m.mem cell
    let v:=CheckDivision.after m cell
    v.reg .x27=quotient (m.reg .x27) b ∧ v.reg .x18=quotient (p2 m b) b ∧
    v.reg .x20=quotient (p1 m b) b ∧ v.reg .x25=quotient (p0 m b) b ∧
    v.reg .x7=rem m b ∧ v.reg .x6=((rem m b) <<< ((m.reg .x15).toNat%64)) ||| m.reg .x6 ∧
    v.mem=m.mem := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

attribute [local irreducible] CheckDivision.after quotient carryWord p2 p1 p0 rem

def limbs (m : Model) := [(m.reg .x27).toNat,(m.reg .x18).toNat,(m.reg .x20).toNat,(m.reg .x25).toNat]

theorem result (m : Model) (cell b : Nat) (small : 0<b ∧ b≤2^31) (base : m.mem cell=W b)
    (h3 h2 h1 h0 : Fin (2^32)) (r3 : m.reg .x27=W h3.val) (r2 : m.reg .x18=W h2.val)
    (r1 : m.reg .x20=W h1.val) (r0 : m.reg .x25=W h0.val) :
    let xs:=[h3.val,h2.val,h1.val,h0.val]
    let out:=HonestDivision.divide b 0 xs
    let v:=CheckDivision.after m cell
    limbs v=out.1 ∧ v.reg .x7=W out.2 ∧
    v.reg .x6=(W out.2 <<< ((m.reg .x15).toNat%64)) ||| m.reg .x6 ∧ v.mem=m.mem := by
  let n3:=h3.val
  let n2:=(n3%b)*limb+h2.val
  let n1:=(n2%b)*limb+h1.val
  let n0:=(n1%b)*limb+h0.val
  have s3:=column 0 h3.val b small small.1 h3.isLt
  simp only [Nat.zero_mul,Nat.zero_add] at s3
  change quotient (W n3) (W b)=_ ∧ carryWord (W h3.val) (W n3) (W b)=W (n3%b) ∧ n3/b<limb ∧ n3%b<b at s3
  have s2:=column (n3%b) h2.val b small s3.2.2.2 h2.isLt
  have s1:=column (n2%b) h1.val b small s2.2.2.2 h1.isLt
  have s0:=column (n1%b) h0.val b small s1.2.2.2 h0.isLt
  have carrySmall {a : Nat} (h : a < b) : a < limb := Nat.lt_of_lt_of_le h (Nat.le_trans small.2 (by decide))
  have wide {a : Nat} (h : a < limb) : a < 2^64 := Nat.lt_of_lt_of_le h (by decide)
  have eq2 : p2 m (W b)=W n2 := by
    rw [p2,r3,r2,s3.2.1,joined _ _ (carrySmall s3.2.2.2) h2.isLt]
  have eq1 : p1 m (W b)=W n1 := by
    rw [p1,eq2,r2,r1,s2.2.1,joined _ _ (carrySmall s2.2.2.2) h1.isLt]
  have eq0 : p0 m (W b)=W n0 := by
    rw [p0,eq1,r1,r0,s1.2.1,joined _ _ (carrySmall s1.2.2.2) h0.isLt]
  have remEq : rem m (W b)=W (n0%b) := by
    rw [rem,eq0];exact last_rem (n1%b) h0.val b small s1.2.2.2 h0.isLt
  obtain ⟨a3,a2,a1,a0,ar,as',am⟩:=shape m cell
  rw [base,r3,s3.1] at a3
  rw [base,eq2,s2.1] at a2
  rw [base,eq1,s1.1] at a1
  rw [base,eq0,s0.1] at a0
  rw [base,remEq] at ar as'
  have out : HonestDivision.divide b 0 [h3.val,h2.val,h1.val,h0.val]=([n3/b,n2/b,n1/b,n0/b],n0%b) := by
    simp only [HonestDivision.divide,HonestDivision.limb,Nat.zero_mul,Nat.zero_add]
    exact congrArg₂ Prod.mk (by simp only [n3,n2,n1,n0,Nat.mod_eq_of_lt s3.2.2.1,Nat.mod_eq_of_lt s2.2.2.1,
      Nat.mod_eq_of_lt s1.2.2.1,Nat.mod_eq_of_lt s0.2.2.1]) rfl
  dsimp only
  rw [out]
  refine ⟨?_,ar,as',am⟩
  simp only [limbs,a3,a2,a1,a0,BitVec.toNat_ofNat]
  change [n3/b%2^64,n2/b%2^64,n1/b%2^64,n0/b%2^64]=[n3/b,n2/b,n1/b,n0/b]
  rw [Nat.mod_eq_of_lt (wide s3.2.2.1),Nat.mod_eq_of_lt (wide s2.2.2.1),
    Nat.mod_eq_of_lt (wide s1.2.2.1),Nat.mod_eq_of_lt (wide s0.2.2.1)]

end CommitGolfCandidate.Reconstruction.CheckDivisionResult
