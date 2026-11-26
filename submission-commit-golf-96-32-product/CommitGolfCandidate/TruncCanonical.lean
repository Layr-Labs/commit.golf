import CommitGolfCandidate.TruncCodec
namespace CommitGolfCandidate.Trunc
open CommitGolf
set_option maxRecDepth 9000
set_option maxHeartbeats 100000
attribute [local irreducible] unpack pack wideIndex narrowIndex

private theorem locallyInverse (b : Bool) (j : Nat) (small : j < (if b then 536 else 32)) :
    ∀ k∈localShort b j,k<(if b then 510 else 30) ∧ localWide b k=j := by
  cases b <;> unfold localShort <;> simp only [ite_true,ite_false,Bool.false_eq_true] at small ⊢
  all_goals split_ifs <;> simp_all [localWide] <;> (try split_ifs) <;> omega

theorem narrow_widen (j k : Nat) (hj : j<72704) (someByte : wideIndex j=some k) :
    k<69120 ∧ narrowIndex k=j := by
  by_cases recs : j<68608
  · have hb : j/536<128 := by omega
    have hx : j%536<536:=Nat.mod_lt _ (by decide)
    have eqn:=blockWide 0 (j/536) (j%536) hb hx
    change wideIndex (536*(j/536)+j%536)=(localShort true (j%536)).map (510*(j/536)+·) at eqn
    rw [show 536*(j/536)+j%536=j by omega,someByte] at eqn
    cases e : localShort true (j%536) with
    | none=>simp [e] at eqn
    | some n=>
      have m:=locallyInverse true (j%536) hx n (by simp [e])
      have h : n<510:=m.1
      simp only [e,Option.map_some,Option.some.injEq] at eqn
      have pos : narrowIndex (510*(j/536)+n)=536*(j/536)+localWide true n := blockNarrow 0 _ _ hb h
      rw [eqn,pos,m.2];constructor <;> omega
  · have hb : (j-68608)/32<128:=by omega
    have hx : (j-68608)%32<32:=Nat.mod_lt _ (by decide)
    have eqn:=blockWide 1 ((j-68608)/32) ((j-68608)%32) hb hx
    change wideIndex (68608+32*((j-68608)/32)+(j-68608)%32)=(localShort false ((j-68608)%32)).map (65280+30*((j-68608)/32)+·) at eqn
    rw [show 68608+32*((j-68608)/32)+(j-68608)%32=j by omega,someByte] at eqn
    cases e : localShort false ((j-68608)%32) with
    | none=>simp [e] at eqn
    | some n=>
      have m:=locallyInverse false ((j-68608)%32) hx n (by simp [e])
      have h : n<30:=m.1
      simp only [e,Option.map_some,Option.some.injEq] at eqn
      have pos : narrowIndex (65280+30*((j-68608)/32)+n)=68608+32*((j-68608)/32)+localWide false n := blockNarrow 1 _ _ hb h
      rw [eqn,pos,m.2];constructor <;> omega

private theorem mappedByte (n : Nat) (f : Nat→Byte) (j : Nat) (h : j<((List.range n).map f).length) :
    ((List.range n).map f)[j]=f j := by simp

private theorem shortByte (p : Proof) (j : Nat) (h : j<(pack p).length) :
    (pack p)[j]=p[narrowIndex j]?.getD 0 := by
  unfold pack at h ⊢;exact mappedByte 69120 _ j h
private theorem paddedByte (p : Proof) (j : Nat) (h : j<(unpack p).length) :
    (unpack p)[j]=((wideIndex j).bind (fun u=>p[u]?)).getD 0 := by
  unfold unpack at h ⊢;exact mappedByte 72704 _ j h

theorem unpackPack (p : Proof) (len : p.length=72704)
    (zero : ∀ j (hj : j<p.length),wideIndex j=none → p[j]=0) : unpack (pack p)=p := by
  apply List.ext_getElem
  · rw [unpack_length,len]
  · intro j hj hp
    have bj : j<72704:=len ▸ hp
    rw [paddedByte (pack p) j hj]
    cases e : wideIndex j with
    | none=>exact (zero j hp e).symm
    | some k=>
      have h:=narrow_widen j k bj e
      have bound : k<(pack p).length:=by rw [pack_length];exact h.1
      rw [Option.bind_some,List.getElem?_eq_getElem bound,Option.getD_some]
      rw [shortByte p k bound,h.2,List.getElem?_eq_getElem hp,Option.getD_some]

private theorem tailHole (j : Nat) (e : localShort false j=none) : 30≤j := by
  by_contra! h
  have eq : localShort false j=some j:=by simp [localShort,h]
  rw [eq] at e;cases e

theorem omitted (j : Nat) (small : j<72704) (hole : wideIndex j=none) :
    (∃ r<128, ∃ l, 3≤l ∧ l<16 ∧ ∃ k,30≤k ∧ k<32 ∧ j=536*r+24+32*l+k) ∨
    (∃ p<128, ∃ k,30≤k ∧ k<32 ∧ j=68608+32*p+k) := by
  by_cases row : j<68608
  · left;rw [wideIndex,if_pos row] at hole
    have e : localShort true (j%536)=none := by
      cases h : localShort true (j%536) with
      | none=>rfl
      | some k=>simp only [h,Option.map_some,reduceCtorEq] at hole
    unfold localShort at e;simp only [ite_true] at e
    split_ifs at e <;> try contradiction
    refine ⟨j/536,by omega,3+(j%536-120)/32,by omega,by omega,(j%536-120)%32,by omega,by omega,by omega⟩
  · right;rw [wideIndex,if_neg row] at hole
    have e : localShort false ((j-68608)%32)=none := by
      cases h : localShort false ((j-68608)%32) with
      | none=>rfl
      | some k=>simp only [h,Option.map_some,reduceCtorEq] at hole
    have lower:=tailHole _ e
    have upper : (j-68608)%32<32:=Nat.mod_lt _ (by decide)
    have group : (j-68608)/32<128:=by omega
    have identity : j=68608+32*((j-68608)/32)+(j-68608)%32:=by omega
    exact ⟨_,group,_,lower,upper,identity⟩
end CommitGolfCandidate.Trunc
