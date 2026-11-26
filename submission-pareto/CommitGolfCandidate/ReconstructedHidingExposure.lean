import CommitGolfCandidate.ReconstructedHidingGenerator

namespace CommitGolfCandidate.Reconstruction.HidingReplay
open CommitGolfCandidate.Permutation CommitGolfCandidate.Permutation.NonceChain Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {S K D R : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype K] [Nonempty K] [Fintype D] [Nonempty D] [Fintype R] [Nonempty R] {n : Nat}

private theorem mean_ind_finset {X : Type} [Fintype X] [DecidableEq X] (vals : Finset X) :
    mean (fun x : X => ind (x ∈ vals)) = vals.card / (Fintype.card X : ℝ) := by
  unfold mean avg
  rw [sum_ind, Finset.card_univ]
  simp

private theorem mean_coordinate {I A : Type} [Fintype I] [Fintype A] [Nonempty A] [DecidableEq I]
    (i : I) (a : A) : mean (fun f : I → A => ind (f i = a)) = 1/(Fintype.card A : ℝ) := by
  classical
  let split := Equiv.funSplitAt i A
  have h := mean_equiv split (fun p => ind (p.1 = a))
  change mean (fun f : I → A => ind (f i = a)) = _ at h
  rw [h, mean_prod (fun v (_ : {j : I // j ≠ i} → A) => ind (v = a))]
  simp only [mean,avg_const Finset.univ_nonempty]
  unfold avg
  rw [sum_ind, Finset.card_univ]
  have singleton : (Finset.univ.filter (fun j : A => j = a)) = {a} := by ext j; simp
  rw [singleton,Finset.card_singleton,Nat.cast_one]

/-- A transcript of input addresses can single out at most one key per address,
provided inputs for different keys anywhere in the schedule are disjoint. -/
theorem used_input_bound (address : K → Fin n → S)
    (unique : ∀ k k' i j, address k i = address k' j → k = k') (used : Finset S) :
    mean (fun k => ind (∃ i, address k i ∈ used)) ≤ used.card / (Fintype.card K : ℝ) := by
  classical
  let decode (a : S) : K := if hit : ∃ k : K, ∃ i, address k i = a then Classical.choose hit else Classical.choice inferInstance
  have recover (k : K) (i : Fin n) : decode (address k i) = k := by
    have h : ∃ l j, address l j = address k i := ⟨k,i,rfl⟩
    obtain ⟨j,eq⟩ := Classical.choose_spec h
    simpa only [decode,dite_eq_left h] using unique (Classical.choose h) k j i eq
  have charge : ∀ k, (∃ i, address k i ∈ used) → k ∈ used.image decode := by
    rintro k ⟨i,h⟩
    exact Finset.mem_image.mpr ⟨address k i,h,recover k i⟩
  calc
    _ ≤ mean (fun k => ind (k ∈ used.image decode)) := avg_mono (fun k _ => ind_mono (charge k))
    _ = _ := mean_ind_finset _
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_image_le) (Nat.cast_nonneg _)

/-- Once all visible parts are distinct, an inverse endpoint has at most one
candidate group. Its reserved coordinates remain independent of the transcript. -/
theorem used_output_bound (split : S ≃ D × R) (d : Fin n → D) (distinct : Function.Injective d)
    (used : Finset S) :
    mean (fun r : Fin n → R => ind (∃ i, split.symm (d i,r i) ∈ used))
      ≤ used.card / (Fintype.card R : ℝ) := by
  classical
  let hit (a : S) (r : Fin n → R) := ∃ i, split.symm (d i,r i) = a
  have one (a : S) : mean (fun r => ind (hit a r)) ≤ 1/(Fintype.card R : ℝ) := by
    by_cases found : ∃ i, d i = (split a).1
    · obtain ⟨i,h⟩ := found
      refine (avg_mono (g := fun r => ind (hit a r)) (h := fun r => ind (r i = (split a).2)) ?_).trans
        (mean_coordinate i (split a).2).le
      intro r _
      apply ind_mono
      rintro ⟨j,eq⟩
      have x := split.symm_apply_eq.mp eq
      have same := distinct ((congrArg Prod.fst x).trans h.symm)
      exact same ▸ congrArg Prod.snd x
    · have impossible (r : Fin n → R) : ¬ hit a r := by
        rintro ⟨j,eq⟩
        exact found ⟨j,congrArg Prod.fst (split.symm_apply_eq.mp eq)⟩
      simp [mean,ind_neg (impossible _),avg_zero]
  have charge (r : Fin n → R) :
      ind (∃ i, split.symm (d i,r i) ∈ used) ≤ ∑ a ∈ used, ind (hit a r) := by
    by_cases someHit : ∃ i, split.symm (d i,r i) ∈ used
    · obtain ⟨i,h⟩ := someHit
      let a := split.symm (d i,r i)
      have eq : ind (hit a r) = 1 := ind_pos ⟨i,rfl⟩
      exact (ind_le_one _).trans (eq ▸ Finset.single_le_sum (f := fun a => ind (hit a r)) (fun _ _ => ind_nonneg _) h)
    · rw [ind_neg someHit]
      exact Finset.sum_nonneg fun _ _ => ind_nonneg _
  refine (avg_mono (fun r _ => charge r)).trans ?_
  rw [avg_sum]
  exact (Finset.sum_le_sum (fun a _ => one a)).trans_eq (by simp [div_eq_mul_inv])

/-- Duplicate visible parts of independent random blocks are an independent
birthday term, charged once for the tape instead of once per inverse query. -/
theorem duplicate_parts_bound :
    mean (fun d : Fin n → D => ind (¬ Function.Injective d)) ≤ (n:ℝ)*n/Fintype.card D := by
  classical
  have bound := exposed_bound (S := D) (fun (_ : Fin n) (v : D) => v)
    (fun _ => Function.injective_id) (∅ : Finset D)
  have bad (d : Fin n → D) : ¬ Function.Injective d → Exposed d (∅ : Finset D) := by
    intro h
    simp only [Function.Injective] at h
    push Not at h
    obtain ⟨i,j,eq,ne⟩ := h
    exact ⟨i, Or.inr ⟨j,Ne.symm ne,eq⟩⟩
  exact (avg_mono (fun d _ => ind_mono (bad d))).trans (by simpa only [Fintype.card_fin,Finset.card_empty,Nat.cast_zero,zero_add,mul_div_assoc] using bound)

end CommitGolfCandidate.Reconstruction.HidingReplay
