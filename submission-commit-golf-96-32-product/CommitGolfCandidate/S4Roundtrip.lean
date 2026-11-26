import CommitGolfCandidate.S4RecordWire
namespace CommitGolfCandidate.S4
open CommitGolf
open Late (Levels SaltTape Digest node bytes)
attribute [local irreducible] List.range List.finRange

private theorem padded30 (v : BitVec 240) :
    (((0 : BitVec 16) ++ v).setWidth 240).setWidth 256=(0 : BitVec 16) ++ v := by
  rw [BitVec.setWidth_append_eq_right]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,Nat.mod_eq_of_lt (by have:=v.isLt;omega)]
  have rhs : ((0 : BitVec 16) ++ v).toNat=v.toNat:=by rw [BitVec.toNat_append];simp
  exact rhs.symm

theorem nodeRoundtrip (H : Compression) (m : Message) (s : SaltTape) (t : Levels) (tree : HonestTree .byte H m s t)
    (h j : Nat) (low : 2≤h) (hi : h<24) :
    ((node t h j).setWidth 240).setWidth 256=node t h j := by
  by_cases bound : j<width h
  · obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : h≠0)
    rw [tree.parent _ (by omega) j bound]
    have bitsEq : bits .byte (k+1)=240:=by unfold bits;rw [if_neg (by omega),if_neg (by intro e;cases e.1)]
    simp only [retained,bitsEq,show (240 : Nat)≠238 by decide,ite_false,ite_true]
    exact padded30 _
  · rw [tree.missing h (by omega) j (by omega)];rfl


end CommitGolfCandidate.S4
