import CommitGolfCandidate.S4Mask238
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

private theorem narrowWide (x : Digest) :
    ((Trunc.pad238 x).setWidth 240).setWidth 256=Trunc.pad238 x := by
  have val : (Trunc.pad238 x).toNat=(x.extractLsb' 0 238).toNat := by
    unfold Trunc.pad238;rw [BitVec.toNat_append];simp
  have limit := (x.extractLsb' 0 238).isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth,BitVec.toNat_setWidth,val]
  rw [Nat.mod_eq_of_lt (show (x.extractLsb' 0 238).toNat<2^240 by omega),
    Nat.mod_eq_of_lt (show (x.extractLsb' 0 238).toNat<2^256 by omega)]
private theorem narrowByte (x : Digest) :
    Carry.lower ((Trunc.pad238 x).extractLsb' 232 8)=(Trunc.pad238 x).extractLsb' 232 8 := by
  unfold Carry.lower
  apply BitVec.eq_of_getLsbD_eq;intro i hi
  rw [BitVec.getLsbD_and,BitVec.getLsbD_extractLsb',Trunc.pad238_bit]
  interval_cases i <;> simp
theorem nodeRoundtrip (H : Compression) (m : Message) (s : SaltTape) (t : Levels) (tree : HonestTree .packed H m s t)
    (h j : Nat) (low : 2≤h) (hi : h<24) :
    ((node t h j).setWidth 240).setWidth 256=node t h j := by
  by_cases bound : j<width h
  · obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : h≠0)
    rw [tree.parent _ (by omega) j bound]
    have shape : bits .packed (k+1)=238 ∨ bits .packed (k+1)=240 := by
      unfold bits;rw [if_neg (by omega)];split <;> simp
    rcases shape with small|wide
    · simp only [retained,small,ite_true]
      exact narrowWide _
    · simp only [retained,wide,show (240 : Nat)≠238 by decide,ite_false,ite_true]
      exact padded30 _
  · rw [tree.missing h (by omega) j (by omega)];rfl

theorem nodeHighByte (H : Compression) (m : Message) (s : SaltTape) (t : Levels) (tree : HonestTree .packed H m s t)
    (h j : Nat) (low : 6≤h) (hi : h<24) :
    Carry.lower ((node t h j).extractLsb' 232 8)=(node t h j).extractLsb' 232 8 := by
  by_cases bound : j<width h
  · obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : h≠0)
    rw [tree.parent _ (by omega) j bound]
    have e : bits .packed (k+1)=238:=by unfold bits;rw [if_neg (by omega),if_pos ⟨rfl,low⟩]
    simp only [retained,e,ite_true]
    exact narrowByte _
  · rw [tree.missing h (by omega) j (by omega)];rfl


end CommitGolfCandidate.S4
