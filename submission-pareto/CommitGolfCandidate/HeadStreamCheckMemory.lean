import CommitGolfCandidate.HeadStreamCheckArithmetic

namespace TwoPermutationPrototype.Packed.Checker.HeadRestore
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open ProofCodec.HeadStream
open PackedOpening.Pack (toNat_w)

def headSlot (k p : Nat) : Prop := p<481*k ∧ p%481=45
instance (k p : Nat) : Decidable (headSlot k p) := inferInstanceAs (Decidable (_ ∧ _))

def prefixByte (B n : Nat) (f : Nat → Byte) (g : Word → Byte) (a : Word) : Byte :=
  if B≤a.toNat ∧ a.toNat<B+n then f (a.toNat-B) else g a

theorem prefix_step (B n : Nat) (f : Nat → Byte) (g : Word → Byte) (a : Word)
    (room : B+n<2^64) :
    (if a=BitVec.ofNat 64 (B+n) then f n else prefixByte B n f g a)=prefixByte B (n+1) f g a := by
  have eq : a=BitVec.ofNat 64 (B+n) ↔ a.toNat=B+n := by
    constructor
    · intro h;rw [h,toNat_w _ room]
    · intro h;apply BitVec.eq_of_toNat_eq;rw [h,toNat_w _ room]
  simp only [eq]
  unfold prefixByte
  by_cases hit : a.toNat=B+n
  · have off : a.toNat-B=n := by omega
    have next : B≤a.toNat ∧ a.toNat<B+(n+1) := by omega
    rw [if_pos hit,if_pos next,off]
  · by_cases inside : B≤a.toNat ∧ a.toNat<B+n
    · have next : B≤a.toNat ∧ a.toNat<B+(n+1) := by omega
      rw [if_neg hit,if_pos inside,if_pos next]
    · have outside : ¬(B≤a.toNat ∧ a.toNat<B+(n+1)) := by omega
      rw [if_neg hit,if_neg inside,if_neg outside]

theorem source_eq_target (k i j : Nat) (kept : ¬headSlot k j) :
    compactSource k i=j ↔ i=compactTarget k j := by
  constructor
  · intro h
    have eq := congrArg (compactTarget k) h
    rwa [target_source] at eq
  · intro h
    rw [h,compact_source_target k j kept]

def bodyByte (k L B : Nat) (Q : Proof) (g : Word → Byte) (p : Nat) (a : Word) : Byte :=
  if B≤a.toNat ∧ a.toNat<B+L ∧ ¬headSlot k (a.toNat-B) ∧ p≤compactTarget k (a.toNat-B)
  then Q.getD (compactTarget k (a.toNat-B)) 0 else g a

theorem body_initial (k L B : Nat) (Q : Proof) (g : Word → Byte) (a : Word)
    (records : 481*k≤L) : bodyByte k L B Q g (L-k) a=g a := by
  unfold bodyByte
  rw [if_neg]
  intro ⟨lo,hi,kept,bound⟩
  have := compact_target_bound k L (a.toNat-B) records (by omega) kept
  omega

theorem prefix_zero (B : Nat) (f : Nat → Byte) (g : Word → Byte) (a : Word) :
    prefixByte B 0 f g a=g a := by
  unfold prefixByte
  rw [if_neg (by omega)]

theorem body_step (k L B p : Nat) (Q : Proof) (g : Word → Byte) (a : Word)
    (records : 481*k≤L) (hp : p<L-k) (room : B+L<2^64) :
    (if a=BitVec.ofNat 64 (B+compactSource k p) then Q.getD p 0 else bodyByte k L B Q g (p+1) a)=
      bodyByte k L B Q g p a := by
  have srcbound : compactSource k p<L := by
    have := Nat.min_le_left k ((p+435)/480)
    unfold compactSource
    omega
  have eq : a=BitVec.ofNat 64 (B+compactSource k p) ↔ a.toNat=B+compactSource k p := by
    constructor
    · intro h;rw [h,toNat_w _ (by omega)]
    · intro h;apply BitVec.eq_of_toNat_eq;rw [h,toNat_w _ (by omega)]
  simp only [eq]
  unfold bodyByte
  by_cases hit : a.toNat=B+compactSource k p
  · have off : a.toNat-B=compactSource k p := by omega
    have target : compactTarget k (a.toNat-B)=p := by rw [off,target_source]
    have inside : B≤a.toNat ∧ a.toNat<B+L ∧ ¬headSlot k (a.toNat-B) ∧ p≤compactTarget k (a.toNat-B) := by
      refine ⟨by omega,by omega,?_,by omega⟩
      rw [off]
      exact source_kept k p
    rw [if_pos hit,if_pos inside,target]
  · rw [if_neg hit]
    by_cases inside : B≤a.toNat ∧ a.toNat<B+L ∧ ¬headSlot k (a.toNat-B)
    · have unequal : compactTarget k (a.toNat-B)≠p := by
        intro h
        have eq := (source_eq_target k p (a.toNat-B) inside.2.2).mpr h.symm
        omega
      have cond : p+1≤compactTarget k (a.toNat-B) ↔ p≤compactTarget k (a.toNat-B) := by omega
      simp only [inside.1,inside.2.1,inside.2.2,true_and,cond]
    · have old : ¬(B≤a.toNat ∧ a.toNat<B+L ∧ ¬headSlot k (a.toNat-B) ∧ p+1≤compactTarget k (a.toNat-B)) := by tauto
      have next : ¬(B≤a.toNat ∧ a.toNat<B+L ∧ ¬headSlot k (a.toNat-B) ∧ p≤compactTarget k (a.toNat-B)) := by tauto
      rw [if_neg old,if_neg next]

end TwoPermutationPrototype.Packed.Checker.HeadRestore
