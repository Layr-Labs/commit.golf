import CommitGolfCandidate.LinkedSaltBad

/-! The linked hybrid. Replacing every keyed or linked generator reply by an independent uniform
reply moves any bounded strategy's acceptance by at most `n (3q + 2n) / |K|`, even when the
strategy knows every extracted salt. As in `CounterSalt.ideal_le_counter`: averaging the replay
over all proposed replies counts the actual replies exactly once, because for each permutation
and key exactly one reply vector follows the schedule; a proposed path whose inputs and replies
are fresh is accepted by the lazily sampled permutation with probability at least `|S|^-n`. -/
namespace CommitGolfCandidate.Permutation.LinkedSalt
open Finset NonceChain
set_option linter.unusedSectionVars false
variable {S K D : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype K] [Nonempty K] [Fintype D] [Nonempty D] {n : Nat}

noncomputable def realProb (split : S ≃ D × K) (σ : Schedule n) (x : Fin n → K → S)
    (g : (Fin n → D) → Strat S Bool) : ℝ :=
  mean fun π : Equiv.Perm S => mean fun k : K =>
    (g (fun i => (split (σ.reply π x k i)).1)).eager π PState.init (fun b _ => CounterSalt.accept b)

/-- For each permutation and key, the real replies are the only replies that follow the schedule. -/
theorem follows_iff (σ : Schedule n) (π : Equiv.Perm S) (x : Fin n → K → S) (k : K)
    (z : Fin n → S) :
    CounterSalt.follows π (σ.input x k z) z ↔ z = σ.reply π x k := by
  constructor
  · intro hf
    have key : ∀ m (i : Fin n), i.val = m → z i = σ.reply π x k i := by
      intro m
      refine Nat.strong_induction_on m ?_
      intro m ih i hi
      rw [← hf i, σ.reply_eq π x k i]
      congr 1
      unfold Schedule.input
      cases hl : σ.link i with
      | none => rfl
      | some j => exact ih j.val (lt_of_lt_of_eq (σ.link_lt i j hl) hi) j rfl
    funext i
    exact key i.val i rfl
  · rintro rfl i
    exact (σ.reply_eq π x k i).symm

private def partition : ((Fin n → D) × (Fin n → K)) ≃ (Fin n → D × K) where
  toFun z i := (z.1 i, z.2 i)
  invFun f := (fun i => (f i).1, fun i => (f i).2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_weight (split : S ≃ D × K) (σ : Schedule n) (x : Fin n → K → S)
    (g : (Fin n → D) → Strat S Bool) :
    (Fintype.card S : ℝ)^n * mean (fun p : Fin n → D => mean (fun k : K => mean (fun h : Fin n → K =>
      CounterSalt.weight (g p) (σ.input x k (fun i => split.symm (p i,h i)))
        (fun i => split.symm (p i,h i))))) = realProb split σ x g := by
  classical
  let F := fun (k : K) (z : Fin n → S) =>
    CounterSalt.weight (g (fun i => (split (z i)).1)) (σ.input x k z) z
  have reorder (k : K) : mean (fun p : Fin n → D => mean (fun h : Fin n → K =>
      CounterSalt.weight (g p) (σ.input x k (fun i => split.symm (p i,h i)))
        (fun i => split.symm (p i,h i)))) = mean (F k) := by
    let e := partition.trans (Equiv.piCongrRight fun _ : Fin n => split.symm)
    rw [← mean_prod, ← mean_equiv e (F k)]
    apply avg_congr
    rintro ⟨p,h⟩ _
    simp [e,F,partition]
    rfl
  rw [mean_swap (fun (p : Fin n → D) (k : K) => _)]
  simp_rw [reorder]
  unfold F CounterSalt.weight
  simp_rw [follows_iff]
  rw [← avg_mul_left]
  apply Eq.trans _ (mean_swap _)
  apply avg_congr
  intro k _
  rw [mean_swap, ← avg_mul_left]
  apply avg_congr
  intro π _
  unfold mean avg
  simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  rw [Finset.sum_ite_eq' univ]
  simp [field]

/-- Outside the bad event the proposed inputs are distinct and the proposed path is fresh. -/
private theorem safe_of_not_bad (σ : Schedule n) (x : Fin n → K → S) (k : K)
    (distinct : Function.Injective fun i => x i k) (y : Fin n → S) (t : Trace S)
    (nb : ¬LinkedBad x k y t) :
    Function.Injective (σ.input x k y) ∧ ¬CounterSalt.Bad (σ.input x k y) y t := by
  have nx : ∀ i, x i k ∉ t.usedIn ∪ univ.image y := fun i hi => nb (Or.inl ⟨i, hi⟩)
  have ne : ¬Exposed y (t.usedIn ∪ t.usedOut) := fun h => nb (Or.inr h)
  have yinj : Function.Injective y := by
    intro i j eq
    by_contra diff
    exact ne ⟨i, Or.inr ⟨j, Ne.symm diff, eq⟩⟩
  have yin : ∀ j, y j ∉ t.usedIn := fun j hj => ne ⟨j, Or.inl (mem_union_left _ hj)⟩
  have yout : ∀ j, y j ∉ t.usedOut := fun j hj => ne ⟨j, Or.inl (mem_union_right _ hj)⟩
  have ximg : ∀ i j, x i k ≠ y j := fun i j eq =>
    nx i (mem_union_right _ (mem_image.mpr ⟨j, mem_univ _, eq.symm⟩))
  have xin : ∀ i, x i k ∉ t.usedIn := fun i hi => nx i (mem_union_left _ hi)
  refine ⟨?_, ?_⟩
  · intro i i' eq
    cases hi : σ.link i with
    | none =>
      cases hi' : σ.link i' with
      | none =>
        simp only [Schedule.input, hi, hi'] at eq
        exact distinct eq
      | some j' =>
        simp only [Schedule.input, hi, hi'] at eq
        exact absurd eq (ximg i j')
    | some j =>
      cases hi' : σ.link i' with
      | none =>
        simp only [Schedule.input, hi, hi'] at eq
        exact absurd eq.symm (ximg i' j)
      | some j' =>
        simp only [Schedule.input, hi, hi'] at eq
        have same := yinj eq
        subst same
        exact σ.link_inj i i' j hi hi'
  · rintro (⟨i, hit⟩ | ⟨i, hit | ⟨j, hj, eq⟩⟩)
    · cases hl : σ.link i with
      | none =>
        simp only [Schedule.input, hl] at hit
        exact xin i hit
      | some j =>
        simp only [Schedule.input, hl] at hit
        exact yin j hit
    · exact yout i hit
    · exact ne ⟨i, Or.inr ⟨j, hj, eq⟩⟩

theorem linked_path_comparison (σ : Schedule n) (x : Fin n → K → S) (k : K)
    (distinct : Function.Injective fun i => x i k) (g : Strat S Bool) (y : Fin n → S) :
    g.exp PState.init (fun b _ => CounterSalt.accept b) ≤
      (Fintype.card S : ℝ)^n * CounterSalt.weight g (σ.input x k y) y +
        g.exp PState.init (fun _ st => ind (LinkedBad x k y st.trace)) := by
  classical
  by_cases inj : Function.Injective (σ.input x k y)
  · refine (CounterSalt.path_comparison g (σ.input x k y) y inj).trans (add_le_add le_rfl ?_)
    apply Strat.exp_mono
    intro _ st
    apply ind_mono
    intro bad
    by_contra nb
    exact (safe_of_not_bad σ x k distinct y st.trace nb).2 bad
  · have all : ∀ t : Trace S, LinkedBad x k y t := fun t => by
      by_contra nb
      exact inj (safe_of_not_bad σ x k distinct y t nb).1
    have one : g.exp PState.init (fun _ st => ind (LinkedBad x k y st.trace)) = 1 := by
      have fun_eq : (fun (_ : Bool) (st : PState S) => ind (LinkedBad x k y st.trace)) =
          fun _ _ => (1 : ℝ) := by
        funext _ st
        exact ind_pos (all _)
      rw [fun_eq]
      exact Strat.exp_const 1 g PState.init Trace.WF.nil
    have w : 0 ≤ CounterSalt.weight g (σ.input x k y) y := by
      unfold CounterSalt.weight
      apply avg_nonneg
      intro π _
      split_ifs
      · exact Strat.eager_nonneg π (fun _ _ => ind_nonneg _) g PState.init
      · exact le_rfl
    have le1 : g.exp PState.init (fun b _ => CounterSalt.accept b) ≤ 1 :=
      Strat.exp_le zero_le_one (fun _ _ => ind_le_one _) g PState.init
    have wpos := mul_nonneg (pow_nonneg (Nat.cast_nonneg (Fintype.card S) : (0 : ℝ) ≤ _) n) w
    rw [one]
    linarith

/-- One-sided event discrepancy of the linked hybrid. Running the strategy with the
complementary event bounds the other direction with the same error. -/
theorem ideal_le_linked (split : S ≃ D × K) (σ : Schedule n) (x : Fin n → K → S)
    (xi : ∀ i, Function.Injective (x i)) (distinct : ∀ k, Function.Injective fun i => x i k)
    (g : (Fin n → D) → Strat S Bool) (q : Nat) (bound : ∀ p, (g p).QB q) :
    NonceChain.idealProb g ≤ realProb split σ x g + n * ((3*q+2*n : ℝ)/Fintype.card K) := by
  rw [← sum_weight split σ x g]
  let err := n * ((3*q+2*n : ℝ)/Fintype.card K)
  change mean _ ≤ _ + err
  rw [← avg_mul_left, ← avg_const (Finset.univ_nonempty (α := Fin n → D)) err, ← avg_add]
  apply avg_mono
  intro p _
  have step (k : K) (h : Fin n → K) := linked_path_comparison σ x k (distinct k) (g p)
    (fun i => split.symm (p i, h i))
  have av := avg_mono (A := univ) (fun k _ => avg_mono (A := univ) (fun h _ => step k h))
  simp only [avg_const Finset.univ_nonempty, avg_add, avg_mul_left] at av
  exact av.trans (add_le_add le_rfl (bad_expectation x xi (fun i h => split.symm (p i, h))
    (fun i a b eq => congrArg Prod.snd (split.symm.injective eq)) (g p) (bound p)))

end CommitGolfCandidate.Permutation.LinkedSalt
