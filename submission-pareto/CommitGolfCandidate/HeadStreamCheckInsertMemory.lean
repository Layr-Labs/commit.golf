import CommitGolfCandidate.HeadStreamCheckLoops

namespace TwoPermutationPrototype.Packed.Checker.HeadRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open ProofCodec.HeadStreamThree
open PackedOpening.Pack (toNat_w)

def installedByte (k B : Nat) (Q : Proof) (g : Word → Byte) (r : Nat) (a : Word) : Byte :=
  if B≤a.toNat ∧ (a.toNat-B)/481<r ∧ (a.toNat-B)%481=45
  then BitVec.ofNat 8 (restoredHead k Q ((a.toNat-B)/481)) else g a

def insertByte (k B : Nat) (Q : Proof) (g : Word → Byte) (r : Nat) (a : Word) : Byte :=
  prefixByte (B+2^33) r (fun _ => 0) (installedByte k B Q g r) a

theorem installed_step (k B r : Nat) (Q : Proof) (g : Word → Byte) (a : Word)
    (room : B+481*r+45<2^64) :
    (if a=BitVec.ofNat 64 (B+481*r+45) then BitVec.ofNat 8 (restoredHead k Q r)
      else installedByte k B Q g r a)=installedByte k B Q g (r+1) a := by
  have eq : a=BitVec.ofNat 64 (B+481*r+45) ↔ a.toNat=B+481*r+45 := by
    constructor
    · intro h;rw [h,toNat_w _ room]
    · intro h;apply BitVec.eq_of_toNat_eq;rw [h,toNat_w _ room]
  simp only [eq]
  unfold installedByte
  by_cases hit : a.toNat=B+481*r+45
  · have quotient : (a.toNat-B)/481=r := by omega
    have next : B≤a.toNat ∧ (a.toNat-B)/481<r+1 ∧ (a.toNat-B)%481=45 := by omega
    rw [if_pos hit,if_pos next,quotient]
  · rw [if_neg hit]
    have same : (B≤a.toNat ∧ (a.toNat-B)/481<r ∧ (a.toNat-B)%481=45) ↔
        (B≤a.toNat ∧ (a.toNat-B)/481<r+1 ∧ (a.toNat-B)%481=45) := by omega
    simp only [same]

theorem prefix_write_below (B n : Nat) (f : Nat → Byte) (g : Word → Byte)
    (target a : Word) (v : Byte) (below : target.toNat<B) :
    (if a=target then v else prefixByte B n f g a)=
      prefixByte B n f (fun q => if q=target then v else g q) a := by
  by_cases hit : a=target
  · subst a
    simp only [ite_true,prefixByte,if_neg (by omega : ¬(B≤target.toNat ∧ target.toNat<B+n))]
  · unfold prefixByte
    by_cases inside : B≤a.toNat ∧ a.toNat<B+n <;> simp only [hit,inside,ite_false,ite_true]

theorem insert_step (k B r : Nat) (Q : Proof) (g : Word → Byte) (a : Word)
    (rk : r<k) (small : 481*k<2^33) (room : B+2^34<2^64) :
    (if a=BitVec.ofNat 64 (B+2^33+r) then 0 else
      if a=BitVec.ofNat 64 (B+481*r+45) then BitVec.ofNat 8 (restoredHead k Q r)
      else insertByte k B Q g r a)=insertByte k B Q g (r+1) a := by
  have hr : B+481*r+45<2^64 := by omega
  have rs : B+2^33+r<2^64 := by omega
  have low : (BitVec.ofNat 64 (B+481*r+45)).toNat<B+2^33 := by rw [toNat_w _ hr];omega
  unfold insertByte
  rw [prefix_write_below _ _ _ _ _ _ _ low]
  have background : (fun q => if q=BitVec.ofNat 64 (B+481*r+45)
      then BitVec.ofNat 8 (restoredHead k Q r) else installedByte k B Q g r q)=
      installedByte k B Q g (r+1) := by
    funext q
    exact installed_step k B r Q g q hr
  rw [background]
  exact prefix_step _ _ _ _ _ rs

end TwoPermutationPrototype.Packed.Checker.HeadRestore
