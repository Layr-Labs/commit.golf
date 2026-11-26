import CommitGolfCandidate.ReconstructedCheckCapParents
import CommitGolfCandidate.ReconstructedCheckCapMembership
import CommitGolfCandidate.ReconstructedHonestSortedFlags

namespace CommitGolfCandidate.Reconstruction.CheckCapQuery
open CommitGolf Binding HonestSizeSchedule CheckCapMembership TwoPermutationPrototype.Sampling
set_option maxRecDepth 14000
set_option maxHeartbeats 1600000

private theorem count (o : Oracle) (e first k n : Nat) (on : Nat→Bool) (child : Nat→Binding.Digest) :
    tally (fun j=>on (first+j)) k*work e + (CheckParentLoop.log o e (first+k) n on child).length=
      tally (fun j=>on (first+j)) (k+n)*work e := by
  induction n generalizing k with
  | zero=>simp [CheckParentLoop.log]
  | succ n ih=>
    let f:=fun j=>on (first+j)
    have h:=ih (k+1)
    change (tally f k+(on (first+k)).toNat)*work e + (CheckParentLoop.log o e (first+(k+1)) n on child).length =
      tally f ((k+1)+n)*work e at h
    have len : (CheckParentStep.rows o e (first+k) on child).length=(on (first+k)).toNat*work e := by
      cases b : on (first+k) <;> simp [CheckParentStep.rows,b,CheckParentCallCopy.log,CheckParentExecution.rows]
    rw [Nat.add_mul,Nat.add_assoc] at h
    change _+((List.range' (first+k) (n+1)).flatMap _).length=_
    rw [List.range'_succ,List.flatMap_cons,List.length_append,len]
    simpa only [CheckParentLoop.log,Nat.add_assoc,Nat.add_comm n 1] using h

theorem level (o : Oracle) (f : Nat→Bool) (d : Nat) (pos : 0<d) (small : d≤9) (child : Nat→Binding.Digest) :
    (CheckCapParents.rows o d (used f d) child).length=population f (d-1)*work (d-1) := by
  let n:=2^(d-1)
  have h:=count o (d-1) n 0 n (used f d) child
  simp only [tally,Nat.zero_mul,Nat.zero_add,Nat.add_zero] at h
  have on : (fun j=>used f d (n+j))=row f (9-(d-1)) := by
    funext j
    have dep:9-(d-1)=(9-d)+1:=by omega
    rw [dep]
    change (row f (9-d) (2*((n+j)-n)+0)||row f (9-d) (2*((n+j)-n)+1))=_
    simp only [Nat.add_sub_cancel_left,Nat.add_zero];rfl
  rw [on] at h;exact h

def fee (f : Nat→Bool) : Nat→Nat
  | 0=>0
  | d+1=>population f d*work d+fee f d

private theorem active_le (f : Nat→Bool) (d hi : Nat) (le : d≤hi) (small : hi≤9) : population f d≤population f hi := by
  induction hi with
  | zero=>
    have z : d=0 := by omega
    subst d
    exact Nat.le_refl _
  | succ hi ih=>
    by_cases eq : d=hi+1
    · subst d;rfl
    exact (ih (by omega) (by omega)).trans (levels_count f (hi+1) (by omega) small).2.2

def cap : Nat→Nat
  | 0=>0
  | d+1=>2^d*work d+cap d

def weight : Nat→Nat
  | 0=>0
  | d+1=>work d+weight d

theorem uniform (f : Nat→Bool) (d : Nat) : fee f d≤cap d := by
  induction d with
  | zero=>rfl
  | succ d ih=>exact Nat.add_le_add (Nat.mul_le_mul_right _ (tally_le _ _)) ih

theorem proportional (f : Nat→Bool) (d : Nat) (small : d≤9) :
    fee f d≤population f 9*weight d := by
  induction d with
  | zero=>simp [fee,weight]
  | succ d ih=>
    rw [weight,Nat.mul_add]
    exact Nat.add_le_add (Nat.mul_le_mul_right _ (active_le f d 9 (by omega) le_rfl)) (ih (by omega))

theorem level9 (f : Nat→Bool) : fee f 9≤2303 ∧ fee f 9≤16*population f 9 := by
  exact ⟨(uniform f 9).trans (by decide),(proportional f 9 (by decide)).trans (by change population f 9*16≤16*population f 9;omega)⟩

private theorem lookup_set (bs : List Bool) (i : Nat) (h : i<bs.length) :
    (fun j=>(bs.set i true)[j]?.getD false)=HonestFlagState.patch (fun j=>bs[j]?.getD false) i := by
  funext j;by_cases eq : j=i
  · subst j;simp [HonestFlagState.patch,List.getElem?_set_self h]
  · simp [HonestFlagState.patch,eq,Ne.symm eq]

private theorem fold (xs : List Index) (bs : List Bool) (len : bs.length=512) :
    tally (fun j=>(xs.foldl Frontier.mark bs)[j]?.getD false) 512≤tally (fun j=>bs[j]?.getD false) 512+xs.length := by
  induction xs generalizing bs with
  | nil=>exact Nat.le_refl _
  | cons x xs ih=>
    have h:=ih (Frontier.mark bs x) (by simp [Frontier.mark,len])
    have valid: x.val/32768<512:=(Frontier.heap_endpoint x).2
    change tally (fun j=>(xs.foldl Frontier.mark (bs.set (x.val/32768) true))[j]?.getD false) 512≤tally (fun j=>(bs.set (x.val/32768) true)[j]?.getD false) 512+xs.length at h
    rw [lookup_set _ _ (len ▸ valid)] at h
    have one:=HonestFlagState.tally_patch (fun j=>bs[j]?.getD false) (x.val/32768) 512
    simp only [ite_eq_left valid] at one
    change tally (fun j=>(List.foldl Frontier.mark (bs.set (x.val/32768) true) xs)[j]?.getD false) 512≤_
    simp only [List.length_cons]
    omega

theorem initial (ps : Positions) : population (CapEntry.flags ps) 9≤ps.card := by
  let xs:=ps.sort (·≤·)
  have h:=fold xs (List.replicate 512 false) (by simp)
  have blank : (fun (j : Nat)=>(List.replicate 512 false)[j]?.getD false)=fun _=>false := by
    funext j;by_cases small:j<512
    · rw [List.getElem?_replicate_of_lt small];rfl
    · rw [List.getElem?_eq_none (by simp;omega)];rfl
  rw [blank,show tally (fun _=>false) 512=0 by decide +kernel,Nat.zero_add] at h
  exact h.trans (by change (ps.sort (·≤·)).length≤ps.card;simp)

theorem at_positions (ps : Positions) : fee (CapEntry.flags ps) 9≤2303 ∧ fee (CapEntry.flags ps) 9≤16*ps.card :=
  ⟨(level9 _).1,(level9 _).2.trans (Nat.mul_le_mul_left _ (initial ps))⟩

end CommitGolfCandidate.Reconstruction.CheckCapQuery

