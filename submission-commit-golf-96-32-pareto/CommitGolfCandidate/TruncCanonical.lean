import CommitGolfCandidate.TruncCodec
namespace CommitGolfCandidate.Trunc
open CommitGolf
set_option maxRecDepth 9000
set_option maxHeartbeats 100000
attribute [local irreducible] unpack pack wideIndex narrowIndex

private theorem locallyInverse (b : Bool) (j : Nat) (small : j < (if b then 528 else 32)) :
    ∀ k∈localShort b j,k<(if b then 502 else 30) ∧ localWide b k=j := by
  cases b <;> unfold localShort <;> simp only [ite_true,ite_false,Bool.false_eq_true] at small ⊢
  all_goals split_ifs <;> simp_all [localWide] <;> (try split_ifs) <;> omega

theorem narrow_widen (j k : Nat) (hj : j<71680) (someByte : wideIndex j=some k) :
    k<68096 ∧ narrowIndex k=j := by
  by_cases recs : j<67584
  · have hb : j/528<128 := by omega
    have hx : j%528<528:=Nat.mod_lt _ (by decide)
    have eqn:=blockWide 0 (j/528) (j%528) hb hx
    change wideIndex (528*(j/528)+j%528)=(localShort true (j%528)).map (502*(j/528)+·) at eqn
    rw [show 528*(j/528)+j%528=j by omega,someByte] at eqn
    cases e : localShort true (j%528) with
    | none=>simp [e] at eqn
    | some n=>
      have m:=locallyInverse true (j%528) hx n (by simp [e])
      have h : n<502:=m.1
      simp only [e,Option.map_some,Option.some.injEq] at eqn
      have pos : narrowIndex (502*(j/528)+n)=528*(j/528)+localWide true n := blockNarrow 0 _ _ hb h
      rw [eqn,pos,m.2];constructor <;> omega
  · have hb : (j-67584)/32<128:=by omega
    have hx : (j-67584)%32<32:=Nat.mod_lt _ (by decide)
    have eqn:=blockWide 1 ((j-67584)/32) ((j-67584)%32) hb hx
    change wideIndex (67584+32*((j-67584)/32)+(j-67584)%32)=(localShort false ((j-67584)%32)).map (64256+30*((j-67584)/32)+·) at eqn
    rw [show 67584+32*((j-67584)/32)+(j-67584)%32=j by omega,someByte] at eqn
    cases e : localShort false ((j-67584)%32) with
    | none=>simp [e] at eqn
    | some n=>
      have m:=locallyInverse false ((j-67584)%32) hx n (by simp [e])
      have h : n<30:=m.1
      simp only [e,Option.map_some,Option.some.injEq] at eqn
      have pos : narrowIndex (64256+30*((j-67584)/32)+n)=67584+32*((j-67584)/32)+localWide false n := blockNarrow 1 _ _ hb h
      rw [eqn,pos,m.2];constructor <;> omega

private theorem mappedByte (n : Nat) (f : Nat→Byte) (j : Nat) (h : j<((List.range n).map f).length) :
    ((List.range n).map f)[j]=f j := by simp

private theorem shortByte (p : Proof) (j : Nat) (h : j<(pack p).length) :
    (pack p)[j]=p[narrowIndex j]?.getD 0 := by
  unfold pack at h ⊢;exact mappedByte 68096 _ j h
private theorem paddedByte (p : Proof) (j : Nat) (h : j<(unpack p).length) :
    (unpack p)[j]=((wideIndex j).bind (fun u=>p[u]?)).getD 0 := by
  unfold unpack at h ⊢;exact mappedByte 71680 _ j h

theorem unpackPack (p : Proof) (len : p.length=71680)
    (zero : ∀ j (hj : j<p.length),wideIndex j=none → p[j]=0) : unpack (pack p)=p := by
  apply List.ext_getElem
  · rw [unpack_length,len]
  · intro j hj hp
    have bj : j<71680:=len ▸ hp
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

theorem omitted (j : Nat) (small : j<71680) (hole : wideIndex j=none) :
    (∃ r<128, ∃ l, 3≤l ∧ l<16 ∧ ∃ k,30≤k ∧ k<32 ∧ j=528*r+16+32*l+k) ∨
    (∃ p<128, ∃ k,30≤k ∧ k<32 ∧ j=67584+32*p+k) := by
  by_cases row : j<67584
  · left;rw [wideIndex,if_pos row] at hole
    have e : localShort true (j%528)=none := by
      cases h : localShort true (j%528) with
      | none=>rfl
      | some k=>simp only [h,Option.map_some,reduceCtorEq] at hole
    unfold localShort at e;simp only [ite_true] at e
    split_ifs at e <;> try contradiction
    refine ⟨j/528,by omega,3+(j%528-112)/32,by omega,by omega,(j%528-112)%32,by omega,by omega,by omega⟩
  · right;rw [wideIndex,if_neg row] at hole
    have e : localShort false ((j-67584)%32)=none := by
      cases h : localShort false ((j-67584)%32) with
      | none=>rfl
      | some k=>simp only [h,Option.map_some,reduceCtorEq] at hole
    have lower:=tailHole _ e
    have upper : (j-67584)%32<32:=Nat.mod_lt _ (by decide)
    have group : (j-67584)/32<128:=by omega
    have identity : j=67584+32*((j-67584)/32)+(j-67584)%32:=by omega
    exact ⟨_,group,_,lower,upper,identity⟩
end CommitGolfCandidate.Trunc
