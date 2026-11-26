import CommitGolfCandidate.S4HonestTree
import CommitGolfCandidate.S4Wire
namespace CommitGolfCandidate.S4
open CommitGolf
open Late (Digest Levels SaltTape node)

def First (v : View) (u : Nat) := (List.range 128).find? (fun r=>bucket v r==u)

private theorem found {v : View} {u r : Nat} (e : First v u=some r) : r<128 ∧ bucket v r=u :=
  ⟨List.mem_range.mp (List.mem_of_find?_eq_some e),beq_iff_eq.mp (List.find?_some (p:=fun r=>bucket v r==u) e)⟩

private theorem absent {v : View} {u : Nat} (e : First v u=none) {r : Nat} (hr : r<128) : bucket v r≠u :=
  fun eqv=>(List.find?_eq_none.mp e r (List.mem_range.mpr hr)) (beq_iff_eq.mpr eqv)

def SlotRule (t : Levels) (v : View) := ∀ j<171,∀ y : Digest,
  ((∀ r<128,bucket v r/2≠j) → node t 16 j=y) →
  (∀ r<128,bucket v r/2=j → node t 15 (2*j+(1-bucket v r%2))=y) → v.slot j=y

theorem canonicalSlots (t : Levels) (ps : Positions) (b : ps.card=128) (v : View)
    (idx : v.idx=recordIndex ps) (slots : ∀ j<171,v.slot j=pairSlot t (ps.sort (·≤·)) j) : SlotRule t v := by
  intro j bj y fallback hit
  rw [slots j bj]
  let xs:=ps.sort (·≤·)
  have len : xs.length=128:=(Finset.length_sort ..).trans b
  have get (r : Nat) (hr : r<xs.length) : v.idx r=xs[r] := by
    rw [idx];change xs[r]?.getD _=xs[r];rw [List.getElem?_eq_getElem hr];rfl
  have up (r : Nat) : nodeIndex (v.idx r).val 16=bucket v r/2:=nextIndex _ 15
  unfold pairSlot
  cases e : xs.find? (fun i=>nodeIndex i.val 16==j) with
  | none=>
    apply fallback;intro r br equal
    have rb : r<xs.length:=by omega
    have ex:=List.find?_eq_none.mp e xs[r] (List.getElem_mem rb)
    exact ex (beq_iff_eq.mpr ((congrArg (fun i : Index=>nodeIndex i.val 16) (get r rb).symm).trans ((up r).trans equal)))
  | some i=>
    obtain ⟨r,br,ir⟩:=List.getElem_of_mem (List.mem_of_find?_eq_some e)
    have vr : v.idx r=i:=(get r br).trans ir
    have chosen := beq_iff_eq.mp (List.find?_some (p:=fun i : Index=>nodeIndex i.val 16==j) e)
    have pair : bucket v r/2=j:=(up r).symm.trans ((congrArg (fun x : Index=>nodeIndex x.val 16) vr).trans chosen)
    have ix : (nodeIndex i.val 15)=bucket v r:=by rw [←vr];rfl
    have digit : (nodeIndex i.val 15%2+0+1)%2=1-bucket v r%2:=by rw [ix];omega
    simpa only [sibling,childPos,show radix 15=2 by decide,chosen,digit] using hit r (by omega) pair

theorem honestBatch (p : Profile) (H : Compression) (m : Message) (s : SaltTape) (t : Levels)
    (tree : HonestTree p H m s t) (v : View) (fields : ∀ r<128,
      v.salt r=s (v.idx r) ∧ v.entry r=m (v.idx r) ∧ ∀ h<15,v.peers r h=truePeers t (v.idx r) h)
    (slot : SlotRule t v) : BatchValid p H v (node t 24 0) := by
  let tab:=lower p H v
  have lo (r : Nat) (br : r<128) : tab r=node t 15 (bucket v r):=
    honestRecord p H m s t tree v r 15 (by decide) (fields r br).1 (fields r br).2.1 (fields r br).2.2
  have lookup (u r : Nat) (e : First v u=some r) : tab r=node t 15 u:= (lo r (found e).1).trans (congrArg (node t 15) (found e).2)
  have pair (j : Nat) (bj : j<171) : batchCap p H v j=node t 16 j := by
    have par := tree.parent 15 (by decide) j bj
    change node t 16 j=retained p 16 (H (Late.parentBlock (node t 15 (2*j)) (node t 15 (2*j+1)))) at par
    change mergePair p H ((First v (2*j)).map tab) ((First v (2*j+1)).map tab) (v.slot j)=_
    cases l : First v (2*j) with
    | none=>
      cases rr : First v (2*j+1) with
      | none=>
        apply slot j bj _ (fun _=>rfl)
        intro r br e;have hl:=absent l br;have hr:=absent rr br;omega
      | some r=>
        have sl : v.slot j=node t 15 (2*j):=slot j bj _ (fun e=>by have a:=found rr;have:=e r a.1;omega)
          (fun q bq e=>by have:=absent l bq;congr 1;omega)
        simp only [mergePair,Option.map_none,Option.map_some,Option.isNone_none,Option.isNone_some,
          Bool.true_and,Bool.false_eq_true,ite_false,Option.getD_none,Option.getD_some,lookup _ _ rr,sl]
        exact par.symm
    | some a=>
      cases rr : First v (2*j+1) with
      | none=>
        have sl : v.slot j=node t 15 (2*j+1):=slot j bj _ (fun e=>by have hb:=found l;have:=e a hb.1;omega)
          (fun q bq e=>by have:=absent rr bq;congr 1;omega)
        simp only [mergePair,Option.map_none,Option.map_some,Option.isNone_none,Option.isNone_some,
          Bool.false_and,Bool.false_eq_true,ite_false,Option.getD_none,Option.getD_some,lookup _ _ l,sl]
        exact par.symm
      | some b=>
        simp only [mergePair,Option.map_some,Option.isNone_some,Bool.false_and,Bool.false_eq_true,ite_false,
          Option.getD_some,lookup _ _ l,lookup _ _ rr]
        exact par.symm
  constructor
  · intro r br
    change (First v (bucket v r)).map tab=some (tab r)
    cases e : First v (bucket v r) with
    | none=>exact False.elim ((absent e br) rfl)
    | some q=>rw [Option.map_some,lookup _ _ e,lo r br]
  · have upperEq (k j : Nat) (limit : k≤8) : upper p H (batchCap p H v) k j=node t (16+k) j := by
      induction k generalizing j with
      | zero=>
        by_cases bj : j<171
        · exact (if_pos bj).trans (pair j bj)
        · exact (if_neg bj).trans (tree.missing 16 (by decide) j (show 171≤j by omega)).symm
      | succ k ih=>
        rw [upper]
        have height : 16+(k+1)=17+k:=by omega
        rw [height]
        by_cases bj : j<width (17+k)
        · rw [if_pos bj,ih _ (by omega),ih _ (by omega)]
          have e:=tree.parent (16+k) (by omega) j (by simpa only [show 16+k+1=17+k by omega] using bj)
          simpa only [show 16+k+1=17+k by omega,row,radix,if_neg (by omega : 16+k≠0),Late.parentBlock] using e.symm
        · rw [if_neg bj];exact (tree.missing (17+k) (by omega) j (by omega)).symm
    exact upperEq 8 0 (by decide)
end CommitGolfCandidate.S4
