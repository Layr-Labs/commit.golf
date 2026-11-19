import CommitGolfCandidate.PinCallFibers

namespace CommitGolfCandidate.Permutation
open Finset
attribute [local instance] Classical.propDecidable
variable {S : Type} [DecidableEq S]

theorem bad_answers_card_le (B : BadSpec S) (k u : Nat) (mk : S → Entry S)
    (hp : ∀ old : Entry S, ∃ F : Finset S, F.card ≤ k ∧ ∀ z, B.pair (mk z) old → z ∈ F)
    (hs : ∃ F : Finset S, F.card ≤ u ∧ ∀ z, B.single (mk z) → z ∈ F)
    (t : Trace S) (good : B.Good t) (A : Finset S) :
    (A.filter fun z => ¬ B.Good (mk z :: t)).card ≤ t.length*k+u := by
  classical
  choose Fp hFp1 hFp2 using hp
  obtain ⟨Fs,hFs1,hFs2⟩ := hs
  refine (Finset.card_le_card (s := A.filter fun z => ¬ B.Good (mk z :: t))
    (t := t.toFinset.biUnion Fp ∪ Fs) ?_).trans ?_
  · intro z hz
    have bad := (Finset.mem_filter.1 hz).2
    rw [B.good_cons_iff] at bad
    simp only [good,and_true,not_and_or,not_forall,not_not] at bad
    rw [Finset.mem_union,Finset.mem_biUnion]
    rcases bad with ⟨old,present,pair⟩ | single
    · exact Or.inl ⟨old,List.mem_toFinset.2 present,hFp2 old z (by simpa using pair)⟩
    · exact Or.inr (hFs2 z single)
  · calc
      (t.toFinset.biUnion Fp ∪ Fs).card ≤ (t.toFinset.biUnion Fp).card+Fs.card :=
        Finset.card_union_le _ _
      _ ≤ t.toFinset.card*k+u := Nat.add_le_add
        (Finset.card_biUnion_le_card_mul _ _ _ fun old _ => hFp1 old) hFs1
      _ ≤ t.length*k+u := Nat.add_le_add_right
        (Nat.mul_le_mul_right _ (List.toFinset_card_le t)) _

theorem forward_bad_card (B : BadSpec S) (k : Nat)
    (hp : ∀ x old, ∃ F : Finset S, F.card ≤ k ∧
      ∀ y, B.pair ⟨.fwd,x,y⟩ old → y ∈ F)
    (hs : ∀ x y, ¬ B.single ⟨.fwd,x,y⟩)
    (t : Trace S) (good : B.Good t) (x : S) (A : Finset S) :
    (A.filter fun y => ¬ B.Good (t.stepF x y)).card ≤ t.length*k := by
  classical
  by_cases cached : x ∈ t.usedIn
  · simp only [Trace.stepF,cached,ite_true,good,not_true_eq_false,Finset.filter_false]
    exact Nat.zero_le _
  · simpa only [Trace.stepF,cached,ite_false,Nat.add_zero] using
      bad_answers_card_le B k 0 (fun y => ⟨.fwd,x,y⟩) (hp x)
        ⟨∅,by simp,fun y h => (hs x y h).elim⟩ t good A

theorem inverse_bad_card (B : BadSpec S) (k u : Nat)
    (hp : ∀ y old, ∃ F : Finset S, F.card ≤ k ∧
      ∀ x, B.pair ⟨.inv,x,y⟩ old → x ∈ F)
    (hs : ∀ y, ∃ F : Finset S, F.card ≤ u ∧
      ∀ x, B.single ⟨.inv,x,y⟩ → x ∈ F)
    (t : Trace S) (good : B.Good t) (y : S) (A : Finset S) :
    (A.filter fun x => ¬ B.Good (t.stepI x y)).card ≤ t.length*k+u := by
  classical
  by_cases cached : y ∈ t.usedOut
  · simp only [Trace.stepI,cached,ite_true,good,not_true_eq_false,Finset.filter_false]
    exact Nat.zero_le _
  · simpa only [Trace.stepI,cached,ite_false] using
      bad_answers_card_le B k u (fun x => ⟨.inv,x,y⟩) (hp y) (hs y) t good A

end CommitGolfCandidate.Permutation
