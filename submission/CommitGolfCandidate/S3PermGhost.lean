import CommitGolfCandidate.S3PermBadEvent

/-!
# Hiding one table entry from a strategy

`abs_exp_ghost_le`: let `t'` be the table `t` with one more entry `g` (a "ghost"). For any
strategy and any `[0, 1]`-valued function of its result, the expectations from `t'` and from `t`
differ by at most the probability that the run from `t` touches the ghost, that is, ends with
`g.inp` among the used inputs or `g.out` among the used outputs.

This is the lazy-sampling step of the hiding proof: an entry that the strategy neither queries
nor is handed by chance cannot influence it. Also here: uniform sampling from a finite type as a
strategy, and a few facts on averages.
-/

set_option linter.unusedSectionVars false

namespace CommitGolfCandidate.Permutation

open Finset

/-! ### More on averages -/

section avg
variable {ι κ : Type}

theorem avg_comm (A : Finset ι) (B : Finset κ) (g : ι → κ → ℝ) :
    avg A (fun i => avg B (g i)) = avg B (fun j => avg A (fun i => g i j)) := by
  unfold avg
  rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm, div_right_comm]

theorem avg_sub (A : Finset ι) (g h : ι → ℝ) :
    avg A (fun i => g i - h i) = avg A g - avg A h := by
  unfold avg
  rw [Finset.sum_sub_distrib, sub_div]

theorem abs_avg_sub_le (A : Finset ι) (g h : ι → ℝ) :
    |avg A g - avg A h| ≤ avg A (fun i => |g i - h i|) := by
  rw [← avg_sub]
  unfold avg
  rw [abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

/-- Averaging over a subset `B` of `A` can only increase the average when the terms outside `B`
are nonpositive and the terms on `B` are replaced by larger nonnegative ones. -/
theorem avg_le_avg_of_subset {A B : Finset ι} {g h : ι → ℝ} (hBA : B ⊆ A)
    (hzero : ∀ i ∈ A, i ∉ B → g i ≤ 0) (hgh : ∀ i ∈ B, g i ≤ h i) (hh : ∀ i ∈ B, 0 ≤ h i) :
    avg A g ≤ avg B h := by
  classical
  unfold avg
  have hsum : ∑ i ∈ A, g i ≤ ∑ i ∈ B, h i := by
    rw [← Finset.sum_sdiff hBA]
    have h1 : ∑ i ∈ A \ B, g i ≤ 0 :=
      Finset.sum_nonpos fun i hi => hzero i (Finset.mem_sdiff.1 hi).1 (Finset.mem_sdiff.1 hi).2
    have h2 := Finset.sum_le_sum hgh
    linarith
  have hσ : 0 ≤ ∑ i ∈ B, h i := Finset.sum_nonneg hh
  rcases B.eq_empty_or_nonempty with rfl | hB
  · have h0 : ∑ i ∈ A, g i ≤ 0 := by simpa using hsum
    simpa using div_nonpos_of_nonpos_of_nonneg h0 (Nat.cast_nonneg A.card)
  · have hBpos : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
    have hle : (B.card : ℝ) ≤ A.card := by exact_mod_cast Finset.card_le_card hBA
    calc (∑ i ∈ A, g i) / A.card ≤ (∑ i ∈ B, h i) / A.card :=
          div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)
      _ ≤ (∑ i ∈ B, h i) / B.card := div_le_div_of_nonneg_left hσ hBpos hle

end avg

/-! ### Tables that differ by one entry -/

namespace Trace
variable {S : Type} [DecidableEq S]

theorem usedIn_perm {t t' : Trace S} {g : Entry S} (hp : t'.Perm (g :: t)) :
    t'.usedIn = insert g.inp t.usedIn := by
  ext x
  simp only [mem_usedIn, hp.mem_iff, List.mem_cons, Finset.mem_insert]
  constructor
  · rintro ⟨e, rfl | he, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e, he, rfl⟩
  · rintro (rfl | ⟨e, he, rfl⟩)
    · exact ⟨g, Or.inl rfl, rfl⟩
    · exact ⟨e, Or.inr he, rfl⟩

theorem usedOut_perm {t t' : Trace S} {g : Entry S} (hp : t'.Perm (g :: t)) :
    t'.usedOut = insert g.out t.usedOut := by
  ext y
  simp only [mem_usedOut, hp.mem_iff, List.mem_cons, Finset.mem_insert]
  constructor
  · rintro ⟨e, rfl | he, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨e, he, rfl⟩
  · rintro (rfl | ⟨e, he, rfl⟩)
    · exact ⟨g, Or.inl rfl, rfl⟩
    · exact ⟨e, Or.inr he, rfl⟩

theorem fwdHits_perm_of_ne {t t' : Trace S} {g : Entry S} (hp : t'.Perm (g :: t)) {x : S}
    (hx : g.inp ≠ x) : t'.fwdHits x = t.fwdHits x := by
  ext y
  simp only [mem_fwdHits, hp.mem_iff, List.mem_cons]
  constructor
  · rintro ⟨e, rfl | he, h1, h2⟩
    · exact absurd h1 hx
    · exact ⟨e, he, h1, h2⟩
  · rintro ⟨e, he, h1, h2⟩
    exact ⟨e, Or.inr he, h1, h2⟩

theorem invHits_perm_of_ne {t t' : Trace S} {g : Entry S} (hp : t'.Perm (g :: t)) {y : S}
    (hy : g.out ≠ y) : t'.invHits y = t.invHits y := by
  ext x
  simp only [mem_invHits, hp.mem_iff, List.mem_cons]
  constructor
  · rintro ⟨e, rfl | he, h1, h2⟩
    · exact absurd h1 hy
    · exact ⟨e, he, h1, h2⟩
  · rintro ⟨e, he, h1, h2⟩
    exact ⟨e, Or.inr he, h1, h2⟩

theorem WF.of_perm {t t' : Trace S} {g : Entry S} (hp : t'.Perm (g :: t)) (h : WF t') :
    WF (g :: t) :=
  ⟨(hp.map Entry.inp).nodup_iff.1 h.inp, (hp.map Entry.out).nodup_iff.1 h.out⟩

variable [Fintype S]

theorem mem_usedIn_stepF (t : Trace S) (x y : S) : x ∈ (t.stepF x y).usedIn := by
  unfold stepF
  split_ifs with h
  · exact h
  · exact mem_usedIn.2 ⟨_, List.mem_cons_self, rfl⟩

theorem mem_usedOut_stepI (t : Trace S) (x y : S) : y ∈ (t.stepI x y).usedOut := by
  unfold stepI
  split_ifs with h
  · exact h
  · exact mem_usedOut.2 ⟨_, List.mem_cons_self, rfl⟩

end Trace

namespace Strat

variable {S : Type} {α : Type}

/-! ### Uniform sampling -/

/-- Draw a uniform element of a nonempty finite type (private coins, not a query). -/
noncomputable def uniform (ι : Type) [Fintype ι] [Nonempty ι] (k : ι → Strat S α) :
    Strat S α :=
  .rand (Fintype.card ι - 1) fun i =>
    k ((Fintype.equivFin ι).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) i))

theorem QB_uniform {ι : Type} [Fintype ι] [Nonempty ι] {k : ι → Strat S α} {n : ℕ}
    (h : ∀ i, QB (k i) n) : QB (uniform ι k) n :=
  .rand _ _ n fun _ => h _

variable [Fintype S] [DecidableEq S]

theorem exp_uniform (ι : Type) [Fintype ι] [Nonempty ι] (k : ι → Strat S α) (s : PState S)
    (f : α → PState S → ℝ) :
    (uniform ι k).exp s f = avg Finset.univ fun i => (k i).exp s f := by
  have hcard : Fintype.card ι - 1 + 1 = Fintype.card ι := Nat.sub_add_cancel Fintype.card_pos
  have hcast : ((Fintype.card ι - 1 + 1 : ℕ) : ℝ) = (Fintype.card ι : ℝ) := by rw [hcard]
  show avg Finset.univ (fun i : Fin (Fintype.card ι - 1 + 1) =>
    (k ((Fintype.equivFin ι).symm (Fin.cast hcard i))).exp s f) = _
  unfold avg
  rw [Finset.card_univ, Finset.card_univ, Fintype.card_fin, hcast]
  congr 1
  exact Fintype.sum_equiv ((finCongr hcard).trans (Fintype.equivFin ι).symm) _ _ fun i => rfl

theorem post_uniform {ι : Type} [Fintype ι] [Nonempty ι] {k : ι → Strat S α} {s : PState S}
    {P : α → PState S → Prop} (h : ∀ i, (k i).post s P) : (uniform ι k).post s P :=
  fun _ => h _

theorem post_suffix (st : Strat S α) (s : PState S) :
    st.post s fun _ s' => s.trace <:+ s'.trace := by
  induction st generalizing s with
  | done a => exact List.suffix_refl _
  | fwd x k ih =>
    exact fun y _ => post_mono (fun a s' h => (Trace.suffix_stepF _ _ _).trans h) (ih y _)
  | inv y k ih =>
    exact fun x _ => post_mono (fun a s' h => (Trace.suffix_stepI _ _ _).trans h) (ih x _)
  | rand n k ih => exact fun i => ih i s

/-- A bound that holds on everything reachable bounds the expectation. -/
theorem exp_le_of_post {P : α → PState S → Prop} {f : α → PState S → ℝ} {c : ℝ}
    {st : Strat S α} {s : PState S} (hs : s.trace.WF) (hP : st.post s P)
    (h : ∀ a s', P a s' → f a s' ≤ c) : st.exp s f ≤ c :=
  (exp_le_exp_of_post hP h).trans_eq (exp_const c st s hs)

/-- Two functions that are within `c` of each other on everything reachable have expectations
within `c`. -/
theorem abs_exp_sub_le_of_post {P : α → PState S → Prop} {f g : α → PState S → ℝ} {c : ℝ}
    {st : Strat S α} {s : PState S} (hs : s.trace.WF) (hP : st.post s P)
    (h : ∀ a s', P a s' → |f a s' - g a s'| ≤ c) : |st.exp s f - st.exp s g| ≤ c := by
  have h1 : st.exp s f ≤ st.exp s g + c := by
    have := exp_le_exp_of_post (f := f) (g := fun a s' => g a s' + c) hP fun a s' hp => by
      have := (abs_le.1 (h a s' hp)).2
      linarith
    rw [exp_add, exp_const c st s hs] at this
    exact this
  have h2 : st.exp s g ≤ st.exp s f + c := by
    have := exp_le_exp_of_post (f := g) (g := fun a s' => f a s' + c) hP fun a s' hp => by
      have := (abs_le.1 (h a s' hp)).1
      linarith
    rw [exp_add, exp_const c st s hs] at this
    exact this
  rw [abs_le]
  constructor <;> linarith

/-! ### The ghost entry -/

/-- The table `t` touches the entry `g`: its input or its output is already used. -/
def Touched (g : Entry S) (t : Trace S) : Prop := g.inp ∈ t.usedIn ∨ g.out ∈ t.usedOut

theorem Touched.mono {g : Entry S} {t t' : Trace S} (h : t <:+ t') (ht : Touched g t) :
    Touched g t' := by
  rcases ht with h1 | h1
  · obtain ⟨e, he, hx⟩ := Trace.mem_usedIn.1 h1
    exact Or.inl (Trace.mem_usedIn.2 ⟨e, h.subset he, hx⟩)
  · obtain ⟨e, he, hx⟩ := Trace.mem_usedOut.1 h1
    exact Or.inr (Trace.mem_usedOut.2 ⟨e, h.subset he, hx⟩)

theorem exp_untouched_zero (g : Entry S) (f : α → ℝ) (st : Strat S α) (s : PState S)
    (h : Touched g s.trace) :
    st.exp s (fun a s' => ind (¬ Touched g s'.trace) * f a) = 0 := by
  rw [exp_congr_of_post (post_suffix st s) (g := fun _ _ => 0), exp_zero]
  intro a s' hs
  rw [ind_neg (not_not.2 (h.mono hs)), zero_mul]

/-- One-sided ghost lemma: the part of the expectation from `t` on runs that do not touch `g`
is at most the expectation from the table `t'` that contains `g`. -/
theorem exp_ghost_le (g : Entry S) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (st : Strat S α)
    (t t' : Trace S) (c c' : ℕ) (hp : t'.Perm (g :: t)) (hwf' : t'.WF) :
    st.exp ⟨t, c⟩ (fun a s' => ind (¬ Touched g s'.trace) * f a) ≤
      st.exp ⟨t', c'⟩ (fun a _ => f a) := by
  induction st generalizing t t' c c' with
  | done a => exact mul_le_of_le_one_left (hf a) (ind_le_one _)
  | rand n k ih => exact avg_mono fun i _ => ih i t t' c c' hp hwf'
  | fwd x k ih =>
    obtain ⟨hwf, hgi, hgo⟩ := (Trace.WF.of_perm hp hwf').of_cons
    have hin := Trace.usedIn_perm hp
    have hout := Trace.usedOut_perm hp
    simp only [Strat.exp]
    by_cases hxg : x = g.inp
    · have hz : ∀ y ∈ t.fwdAns x, (k y).exp ⟨t.stepF x y, c + 1⟩
          (fun a s' => ind (¬ Touched g s'.trace) * f a) = 0 := fun y _ =>
        exp_untouched_zero g f (k y) _
          (Or.inl (by rw [← hxg]; exact Trace.mem_usedIn_stepF t x y))
      rw [avg_congr hz, avg_zero]
      exact avg_nonneg fun y _ => exp_nonneg (fun a _ => hf a) _ _
    · by_cases hx : x ∈ t.usedIn
      · have hx' : x ∈ t'.usedIn := by rw [hin]; exact Finset.mem_insert_of_mem hx
        have e1 : t.fwdAns x = t.fwdHits x := if_pos hx
        have e2 : t'.fwdAns x = t.fwdHits x :=
          (if_pos hx').trans (Trace.fwdHits_perm_of_ne hp (Ne.symm hxg))
        have e3 : ∀ y, t.stepF x y = t := fun y => if_pos hx
        have e4 : ∀ y, t'.stepF x y = t' := fun y => if_pos hx'
        simp only [e1, e2, e3, e4]
        exact avg_mono fun y _ => ih y t t' _ _ hp hwf'
      · have hx' : x ∉ t'.usedIn := by
          rw [hin, Finset.mem_insert]
          exact fun h => h.elim hxg hx
        have e1 : t.fwdAns x = t.freeOut := if_neg hx
        have e2 : t'.fwdAns x = t.freeOut.erase g.out := by
          rw [Trace.fwdAns, if_neg hx']
          ext y
          simp only [Trace.mem_freeOut, Finset.mem_erase, hout, Finset.mem_insert]
          tauto
        have e3 : ∀ y, t.stepF x y = ⟨.fwd, x, y⟩ :: t := fun y => if_neg hx
        have e4 : ∀ y, t'.stepF x y = ⟨.fwd, x, y⟩ :: t' := fun y => if_neg hx'
        simp only [e1, e2, e3, e4]
        refine avg_le_avg_of_subset (Finset.erase_subset _ _) ?_ ?_ ?_
        · intro y hy hny
          have hyg : y = g.out := by
            by_contra hne
            exact hny (Finset.mem_erase.2 ⟨hne, hy⟩)
          subst hyg
          exact (exp_untouched_zero g f (k g.out) _
            (Or.inr (Trace.mem_usedOut.2 ⟨⟨.fwd, x, g.out⟩, List.mem_cons_self, rfl⟩))).le
        · intro y hy
          have hyo : y ∉ t'.usedOut := by
            rw [hout, Finset.mem_insert]
            rintro (h | h)
            · exact (Finset.mem_erase.1 hy).1 h
            · exact (Trace.mem_freeOut.1 (Finset.mem_erase.1 hy).2) h
          exact ih y _ _ _ _ ((hp.cons _).trans (List.Perm.swap _ _ _)) (hwf'.cons hx' hyo)
        · intro y _
          exact exp_nonneg (fun a _ => hf a) _ _
  | inv y k ih =>
    obtain ⟨hwf, hgi, hgo⟩ := (Trace.WF.of_perm hp hwf').of_cons
    have hin := Trace.usedIn_perm hp
    have hout := Trace.usedOut_perm hp
    simp only [Strat.exp]
    by_cases hyg : y = g.out
    · have hz : ∀ x ∈ t.invAns y, (k x).exp ⟨t.stepI x y, c + 1⟩
          (fun a s' => ind (¬ Touched g s'.trace) * f a) = 0 := fun x _ =>
        exp_untouched_zero g f (k x) _
          (Or.inr (by rw [← hyg]; exact Trace.mem_usedOut_stepI t x y))
      rw [avg_congr hz, avg_zero]
      exact avg_nonneg fun x _ => exp_nonneg (fun a _ => hf a) _ _
    · by_cases hy : y ∈ t.usedOut
      · have hy' : y ∈ t'.usedOut := by rw [hout]; exact Finset.mem_insert_of_mem hy
        have e1 : t.invAns y = t.invHits y := if_pos hy
        have e2 : t'.invAns y = t.invHits y :=
          (if_pos hy').trans (Trace.invHits_perm_of_ne hp (Ne.symm hyg))
        have e3 : ∀ x, t.stepI x y = t := fun x => if_pos hy
        have e4 : ∀ x, t'.stepI x y = t' := fun x => if_pos hy'
        simp only [e1, e2, e3, e4]
        exact avg_mono fun x _ => ih x t t' _ _ hp hwf'
      · have hy' : y ∉ t'.usedOut := by
          rw [hout, Finset.mem_insert]
          exact fun h => h.elim hyg hy
        have e1 : t.invAns y = t.freeIn := if_neg hy
        have e2 : t'.invAns y = t.freeIn.erase g.inp := by
          rw [Trace.invAns, if_neg hy']
          ext x
          simp only [Trace.mem_freeIn, Finset.mem_erase, hin, Finset.mem_insert]
          tauto
        have e3 : ∀ x, t.stepI x y = ⟨.inv, x, y⟩ :: t := fun x => if_neg hy
        have e4 : ∀ x, t'.stepI x y = ⟨.inv, x, y⟩ :: t' := fun x => if_neg hy'
        simp only [e1, e2, e3, e4]
        refine avg_le_avg_of_subset (Finset.erase_subset _ _) ?_ ?_ ?_
        · intro x hx hnx
          have hxg : x = g.inp := by
            by_contra hne
            exact hnx (Finset.mem_erase.2 ⟨hne, hx⟩)
          subst hxg
          exact (exp_untouched_zero g f (k g.inp) _
            (Or.inl (Trace.mem_usedIn.2 ⟨⟨.inv, g.inp, y⟩, List.mem_cons_self, rfl⟩))).le
        · intro x hx
          have hxi : x ∉ t'.usedIn := by
            rw [hin, Finset.mem_insert]
            rintro (h | h)
            · exact (Finset.mem_erase.1 hx).1 h
            · exact (Trace.mem_freeIn.1 (Finset.mem_erase.1 hx).2) h
          exact ih x _ _ _ _ ((hp.cons _).trans (List.Perm.swap _ _ _)) (hwf'.cons hxi hy')
        · intro x _
          exact exp_nonneg (fun a _ => hf a) _ _

/-- **Ghost lemma.** If `t'` is `t` plus the entry `g`, the expectations of a `[0, 1]`-valued
function of the result from `t'` and from `t` differ by at most the probability that the run
from `t` touches `g`. -/
theorem abs_exp_ghost_le (g : Entry S) (f : α → ℝ) (hf0 : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1)
    (st : Strat S α) (t t' : Trace S) (c c' : ℕ) (hp : t'.Perm (g :: t)) (hwf' : t'.WF) :
    |st.exp ⟨t', c'⟩ (fun a _ => f a) - st.exp ⟨t, c⟩ (fun a _ => f a)| ≤
      st.exp ⟨t, c⟩ (fun _ s' => ind (Touched g s'.trace)) := by
  have hwf : t.WF := (Trace.WF.of_perm hp hwf').of_cons.1
  have key : ∀ f' : α → ℝ, (∀ a, 0 ≤ f' a) → (∀ a, f' a ≤ 1) →
      st.exp ⟨t, c⟩ (fun a _ => f' a) ≤ st.exp ⟨t', c'⟩ (fun a _ => f' a) +
        st.exp ⟨t, c⟩ (fun _ s' => ind (Touched g s'.trace)) := by
    intro f' h0 h1
    have hpt : ∀ (a : α) (s' : PState S),
        f' a ≤ ind (¬ Touched g s'.trace) * f' a + ind (Touched g s'.trace) := by
      intro a s'
      by_cases hT : Touched g s'.trace
      · rw [ind_pos hT, ind_neg (not_not.2 hT)]
        linarith [h1 a]
      · rw [ind_neg hT, ind_pos hT]
        linarith
    calc st.exp ⟨t, c⟩ (fun a _ => f' a)
        ≤ st.exp ⟨t, c⟩
            (fun a s' => ind (¬ Touched g s'.trace) * f' a + ind (Touched g s'.trace)) :=
          exp_mono hpt st _
      _ = st.exp ⟨t, c⟩ (fun a s' => ind (¬ Touched g s'.trace) * f' a) +
            st.exp ⟨t, c⟩ (fun _ s' => ind (Touched g s'.trace)) := exp_add _ _ st _
      _ ≤ _ := add_le_add (exp_ghost_le g f' h0 st t t' c c' hp hwf') (le_refl _)
  have k1 := key f hf0 hf1
  have k2 := key (fun a => 1 - f a) (fun a => by linarith [hf1 a]) (fun a => by linarith [hf0 a])
  have e1 : st.exp ⟨t, c⟩ (fun a _ => 1 - f a) = 1 - st.exp ⟨t, c⟩ (fun a _ => f a) :=
    exp_one_sub (f := fun a _ => f a) st ⟨t, c⟩ hwf
  have e2 : st.exp ⟨t', c'⟩ (fun a _ => 1 - f a) = 1 - st.exp ⟨t', c'⟩ (fun a _ => f a) :=
    exp_one_sub (f := fun a _ => f a) st ⟨t', c'⟩ hwf'
  rw [e1, e2] at k2
  rw [abs_le]
  constructor <;> linarith

end Strat

end CommitGolfCandidate.Permutation
