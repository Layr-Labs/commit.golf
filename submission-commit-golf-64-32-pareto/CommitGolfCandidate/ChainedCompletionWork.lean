import CommitGolfCandidate.ChainedCompletionCounter

/-! Weighted completed-chain work, including a completion forecast before its reply. -/
namespace CommitGolfCandidate.Chained
open scoped BigOperators

abbrev CompletedSlot (enc : Encoding) (calls : Height → Nat) (trace : Trace) :=
  (h : Height) × {seed : Seed // Completed enc calls trace (h,seed)}

namespace CompletedSlot
variable {enc : Encoding} {calls : Height → Nat} {trace : Trace}

def identity (slot : CompletedSlot enc calls trace) : Height × Seed := (slot.1,slot.2.val)

theorem identity_injective : Function.Injective (identity (enc := enc) (calls := calls) (trace := trace)) := by
  rintro ⟨h,s⟩ ⟨k,t⟩ same
  obtain ⟨height,seed⟩ := Prod.mk.inj same
  change h = k at height
  change s.val = t.val at seed
  subst k
  have equal : s = t := Subtype.ext seed
  cases equal
  rfl

noncomputable def evaluation (slot : CompletedSlot enc calls trace) : Evaluation enc calls trace :=
  Classical.choose slot.2.property

theorem evaluation_identity (slot : CompletedSlot enc calls trace) :
    slot.evaluation.identity = slot.identity := Classical.choose_spec slot.2.property

end CompletedSlot

theorem counter_work {enc : Encoding} {calls : Height → Nat} {trace : Trace} (good : Good enc trace) :
    (∑ h, calls h*completedCount enc calls trace h) ≤ trace.size := by
  classical
  letI types : ∀ h, Fintype {seed : Seed // Completed enc calls trace (h,seed)} := fun _ => Fintype.ofFinite _
  let index := (Fintype.equivFin (CompletedSlot enc calls trace)).symm
  let family := fun i => (index i).evaluation
  have identities : ∀ i, (family i).identity = (index i).identity := fun i => (index i).evaluation_identity
  have distinct : Function.Injective (fun i => (family i).identity) := by
    intro i j same
    apply index.injective
    apply CompletedSlot.identity_injective
    exact (identities i).symm.trans (same.trans (identities j))
  have bounded := completed_work_bound good family distinct
  have sums : (∑ i, calls (family i).height) = ∑ slot : CompletedSlot enc calls trace, calls slot.1 :=
    Fintype.sum_equiv index _ _ fun i => congrArg calls (congrArg Prod.fst (identities i))
  rw [sums] at bounded
  have counts : ∀ h, Fintype.card {seed : Seed // Completed enc calls trace (h,seed)} =
      completedCount enc calls trace h := fun h =>
        @Set.fintypeCard_eq_ncard Seed (completedSeeds enc calls trace h) (types h)
  calc
    _ = ∑ slot : CompletedSlot enc calls trace, calls slot.1 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro h _
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,counts]
      exact Nat.mul_comm _ _
    _ ≤ _ := bounded

theorem bump_work (calls : Height → Nat) (id : Height × Seed) :
    (∑ h, calls h*bump (some id) h) = calls id.1 := by
  classical
  obtain ⟨height,seed⟩ := id
  rw [Finset.sum_eq_single height]
  · simp [bump]
  · intro h _ different
    simp [bump,Ne.symm different]
  · intro missing
    exact (missing (Finset.mem_univ height)).elim

theorem predicted_work {enc : Encoding} {calls : Height → Nat} {trace : Trace}
    {input : Input} {fresh : ∀ i, trace.input i ≠ input} (good : Good enc trace)
    (small : 2*trace.size < 2^256) :
    (∑ h, calls h*(completedCount enc calls trace h+bump (prediction enc calls trace input fresh) h)) ≤
      trace.size+1 := by
  obtain ⟨reply,safe⟩ := exists_safe_output enc trace small
  have extended := good_append enc trace good input reply fresh safe
  have bounded := counter_work (calls := calls) extended
  change (∑ h, calls h*completedCount enc calls (trace.append input reply fresh) h) ≤ trace.size+1 at bounded
  simpa only [counter_update reply extended small] using bounded

end CommitGolfCandidate.Chained
