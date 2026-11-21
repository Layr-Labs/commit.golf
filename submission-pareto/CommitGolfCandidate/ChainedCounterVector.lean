import CommitGolfCandidate.ChainedCompletionCounter
import CommitGolfCandidate.WeightedAdvance

/-! A common counter vector for internal completions and the permutation hazard. -/
namespace CommitGolfCandidate.Chained.Counters
open scoped BigOperators

abbrev Index := Option Height

def rate (calls : Height → Nat) : Index → Nat
  | none => 1
  | some h => calls h

def widths (width : Height → Nat) : Index → Nat
  | none => 238
  | some h => width h

def interiorKind (predicted : Option (Height × Seed)) : Option Index :=
  predicted.map (fun id => some id.1)

theorem work_split (calls : Height → Nat) (counts : Index → Nat) :
    Weighted.work (rate calls) counts = counts none+∑ h, calls h*counts (some h) := by
  simp only [Weighted.work,Fintype.sum_option,rate,one_mul]

theorem advance_interior_leaf (counts : Index → Nat) (predicted : Option (Height × Seed)) :
    Weighted.advance counts (interiorKind predicted) none = counts none := by
  cases predicted with
  | none => rfl
  | some id => simp [interiorKind,Weighted.advance]

theorem advance_interior_height (counts : Index → Nat) (predicted : Option (Height × Seed)) (h : Height) :
    Weighted.advance counts (interiorKind predicted) (some h) = counts (some h)+bump predicted h := by
  cases predicted with
  | none => simp [interiorKind,Weighted.advance,bump]
  | some id =>
    obtain ⟨k,seed⟩ := id
    by_cases same : k=h
    · subst h
      simp [interiorKind,Weighted.advance,bump]
    · have different : some h ≠ some k := fun equal => same (Option.some.inj equal).symm
      simp [interiorKind,Weighted.advance,bump,same,different]

theorem work_advance_interior (calls : Height → Nat) (counts : Index → Nat) (predicted : Option (Height × Seed)) :
    Weighted.work (rate calls) (Weighted.advance counts (interiorKind predicted)) =
      counts none+∑ h, calls h*(counts (some h)+bump predicted h) := by
  simp only [work_split,advance_interior_leaf,advance_interior_height]

theorem advance_leaf_leaf (counts : Index → Nat) :
    Weighted.advance counts (some none) none = counts none+1 := by
  simp [Weighted.advance]

theorem advance_leaf_height (counts : Index → Nat) (h : Height) :
    Weighted.advance counts (some none) (some h) = counts (some h) := by
  simp [Weighted.advance]

theorem work_advance_leaf (calls : Height → Nat) (counts : Index → Nat) :
    Weighted.work (rate calls) (Weighted.advance counts (some none)) = Weighted.work (rate calls) counts+1 := by
  rw [work_split,work_split]
  simp only [advance_leaf_leaf,advance_leaf_height]
  omega

end CommitGolfCandidate.Chained.Counters
