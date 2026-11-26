import CommitGolfCandidate.LateTrapdoor
import CommitGolfCandidate.S4Auth
namespace CommitGolfCandidate.S4
open CommitGolf
open Late (Levels SaltTape Trapdoor TrapdoorAgrees node nodeAddress rowAddress unusedSlotAddr slice)

theorem siblingRow (td : Trapdoor) (t : Levels) (s : SaltTape) (agree : TrapdoorAgrees td t s)
    (i : Index) (h k : Nat) (bh : h<24) (bk : k<radix h) :
    slice td (rowAddress h (nodeIndex i.val (h+1))+32*k) 32=
      node t h (radix h*nodeIndex i.val (h+1)+k) := by
  let p:=nodeIndex i.val (h+1)
  have within : p<Late.levelCount (h+1):=by
    rw [Late.levelCount,Nat.min_eq_left (by omega)];exact indexInside i (h+1)
  let j:=radix h*p+k
  by_cases real : j<Late.levelCount h
  · exact (congrArg (fun a=>slice td a 32) (Late.row_slot h p k bk).symm).trans (agree.nodes h (by change h≤24;omega) j real)
  · have gap : Late.Padding h p k := ⟨bh,within,by unfold radix at bk;split at bk <;> omega,Or.inr (by omega)⟩
    exact (agree.padding h p k gap).trans (agree.missing h (by change h≤24;omega) j (by omega)).symm

theorem sourceSibling (td : Trapdoor) (t : Levels) (s : SaltTape) (agree : TrapdoorAgrees td t s)
    (i : Index) (h k : Nat) (bh : h<24) :
    slice td (rowAddress h (nodeIndex i.val (h+1))+32*((childPos i.val h+k+1)%radix h)) 32=sibling t i.val h k :=
  siblingRow td t s agree i h _ bh (Nat.mod_lt _ (by unfold radix;split <;> decide))

def marks (positions : List Index) (u : Nat) := positions.any (fun i=>nodeIndex i.val 15==u)
def chooseSlot (t : Levels) (xs : List Index) (j : Nat) :=
  if marks xs (2*j) then node t 15 (2*j+1) else if marks xs (2*j+1) then node t 15 (2*j) else node t 16 j

private theorem bucketSibling (t : Levels) (i : Index) (j : Nat) (hit : nodeIndex i.val 16=j) :
    sibling t i.val 15 0=node t 15 (2*j+1-nodeIndex i.val 15%2) := by
  unfold sibling childPos
  rw [hit,show radix 15=2 by decide];congr 1;omega

theorem orderedSlot (t : Levels) (xs : List Index) (sorted : xs.Pairwise (·≤·)) (j : Nat) :
    pairSlot t xs j=chooseSlot t xs j := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    have ord:=List.pairwise_cons.mp sorted
    have next : nodeIndex x.val 16=nodeIndex x.val 15/2:=nextIndex x.val 15
    by_cases hit : nodeIndex x.val 16=j
    · have ix : nodeIndex x.val 15=2*j ∨ nodeIndex x.val 15=2*j+1:=by omega
      rw [pairSlot,List.find?_cons_of_pos (p:=fun a : Index=>nodeIndex a.val 16==j) (beq_iff_eq.mpr hit)]
      change sibling t x.val 15 0=_
      rw [bucketSibling _ _ _ hit]
      rcases ix with left|right
      · simp only [chooseSlot,marks,List.any_cons,left,beq_self_eq_true,Bool.true_or,ite_true];congr 1;omega
      · have none : marks xs (2*j)=false := by
          apply Bool.eq_false_iff.mpr
          intro yes
          obtain ⟨z,mem,hz⟩:=List.any_eq_true.mp yes
          have lower : nodeIndex x.val 15≤nodeIndex z.val 15:=Nat.div_le_div_right (ord.1 z mem)
          have eqv := beq_iff_eq.mp hz
          omega
        have ne : ¬(2*j+1=2*j):=by omega
        simp only [chooseSlot,marks,List.any_cons,right,beq_eq_false_iff_ne.mpr ne,decide_false,Bool.false_or,
          show xs.any (fun x=>nodeIndex x.val 15==2*j)=false from none, Bool.false_eq_true,ite_false,
          beq_self_eq_true,Bool.true_or,ite_true];congr 1;omega
    · have l : (nodeIndex x.val 15==2*j)=false:=beq_eq_false_iff_ne.mpr (by omega)
      have r : (nodeIndex x.val 15==2*j+1)=false:=beq_eq_false_iff_ne.mpr (by omega)
      have no : (nodeIndex x.val 16==j)=false:=beq_eq_false_iff_ne.mpr hit
      have e:=ih ord.2
      simp only [pairSlot,List.find?_cons,no,Bool.false_eq_true,ite_false,chooseSlot,marks,List.any_cons,l,r,Bool.false_or] at e ⊢
      exact e
end CommitGolfCandidate.S4
