import CommitGolfCandidate.S3PermHiding

/-!
# A counter-mode generator in the lazy permutation model

`GenCall.gen_bound`: a game draws a uniform seed `r`, forward-queries the permutation at the
inputs `enc (r, k)` of a list of distinct counters `k` and hands the parts `out (π (enc (r, k)))`
to the adversary. The adversary (two stages, both with forward and inverse access and private
coins; the first stage runs before the seed is drawn) cannot tell this from independent uniform
parts: with `Q = q1 + L + q2` (`L` blocks, `F` states per part) the acceptance probabilities differ
by at most `2 Q / |R| + 4 Q L / F`.

Proof, from a table `T` reached by the first stage:

1. Seeds for which some generator input is already in `T` are at most `|T|` (`enc` is injective).
2. For any other seed the generator queries are fresh; their entries are ghosts for the second
   stage (`abs_exp_ghosts_le`, the several-entry form of `abs_exp_ghost_le`): running the second
   stage from `T` instead changes its acceptance by at most the probability that it touches a
   ghost input or a ghost output.
3. The replies of fresh queries are drawn without repetition from the unused outputs; as a list
   they are within `L (|T| + L) / |S|` of independent uniform states (`abs_exp_replies_sub_le`),
   and the `out` parts of independent uniform states are independent uniform parts (`out` is
   regular).
4. Ghost inputs: the second stage, run from `T`, does not depend on the seed and makes at most
   `q2` new inputs, each the generator input of at most one seed: `q2 / |R|` on average.
   Ghost outputs: given its parts, a block's reply is uniform in a fiber of `F` states, and the
   run uses at most `|T| + q2` outputs: `L (|T| + q2) / F`.

Mathlib only, on the definitions of `S3PermModel`.
-/

set_option linter.unusedSectionVars false

namespace CommitGolfCandidate.Permutation

open Finset

/-! ### Averages over products, equivalences and independent draws -/

section avg
variable {ι κ : Type}

theorem avg_univ_prod [Fintype ι] [Fintype κ] (g : ι × κ → ℝ) :
    avg (univ : Finset (ι × κ)) g = avg univ fun i => avg univ fun j => g (i, j) := by
  simp only [avg, Finset.card_univ, Fintype.card_prod, Nat.cast_mul]
  rw [Fintype.sum_prod_type, ← Finset.sum_div, div_div, mul_comm (Fintype.card κ : ℝ)]

theorem avg_univ_equiv [Fintype ι] [Fintype κ] (e : ι ≃ κ) (g : κ → ℝ) :
    avg univ (fun i => g (e i)) = avg univ g := by
  unfold avg
  rw [Finset.card_univ, Finset.card_univ, Fintype.card_congr e,
    Fintype.sum_equiv e (fun i => g (e i)) g fun _ => rfl]

open Classical in
theorem ind_exists_le_sum (I : Finset κ) (p : κ → Prop) :
    ind (∃ k ∈ I, p k) ≤ ∑ k ∈ I, ind (p k) := by
  by_cases h : ∃ k ∈ I, p k
  · obtain ⟨k, hk, hp⟩ := h
    rw [ind_pos ⟨k, hk, hp⟩]
    have h1 : ind (p k) ≤ ∑ k ∈ I, ind (p k) :=
      Finset.single_le_sum (f := fun k => ind (p k)) (fun _ _ => ind_nonneg _) hk
    rw [ind_pos hp] at h1
    exact h1
  · rw [ind_neg h]
    exact Finset.sum_nonneg fun _ _ => ind_nonneg _

end avg

/-- The average of `φ` over `n` independent uniform draws from the finite type `ι`. -/
noncomputable def iidAvg (ι : Type) [Fintype ι] : ℕ → (List ι → ℝ) → ℝ
  | 0, φ => φ []
  | n + 1, φ => avg univ fun i => iidAvg ι n fun is => φ (i :: is)

section iid
variable {ι : Type} [Fintype ι]

theorem iidAvg_mono : ∀ {n : ℕ} {φ ψ : List ι → ℝ}, (∀ is, φ is ≤ ψ is) →
    iidAvg ι n φ ≤ iidAvg ι n ψ
  | 0, _, _, h => h []
  | n + 1, _, _, h => avg_mono fun i _ => iidAvg_mono (n := n) fun is => h (i :: is)

theorem iidAvg_nonneg : ∀ {n : ℕ} {φ : List ι → ℝ}, (∀ is, 0 ≤ φ is) → 0 ≤ iidAvg ι n φ
  | 0, _, h => h []
  | n + 1, _, h => avg_nonneg fun i _ => iidAvg_nonneg (n := n) fun is => h (i :: is)

theorem iidAvg_le {c : ℝ} (hc : 0 ≤ c) : ∀ {n : ℕ} {φ : List ι → ℝ}, (∀ is, φ is ≤ c) →
    iidAvg ι n φ ≤ c
  | 0, _, h => h []
  | n + 1, _, h => avg_le hc fun i _ => iidAvg_le hc (n := n) fun is => h (i :: is)

theorem iidAvg_add : ∀ (n : ℕ) (φ ψ : List ι → ℝ),
    iidAvg ι n (fun is => φ is + ψ is) = iidAvg ι n φ + iidAvg ι n ψ
  | 0, _, _ => rfl
  | n + 1, φ, ψ => by
    simp only [iidAvg]
    rw [← avg_add]
    exact avg_congr fun i _ => iidAvg_add n (fun is => φ (i :: is)) (fun is => ψ (i :: is))

theorem iidAvg_avg {κ : Type} (A : Finset κ) : ∀ (n : ℕ) (F : κ → List ι → ℝ),
    avg A (fun j => iidAvg ι n (F j)) = iidAvg ι n (fun is => avg A fun j => F j is)
  | 0, _ => rfl
  | n + 1, F => by
    simp only [iidAvg]
    rw [avg_comm]
    exact avg_congr fun i _ => iidAvg_avg A n (fun j is => F j (i :: is))

/-- `n` independent uniform draws are a uniform `n`-tuple. -/
theorem iidAvg_ofFn : ∀ (n : ℕ) (φ : List ι → ℝ),
    iidAvg ι n φ = avg univ (fun v : Fin n → ι => φ (List.ofFn v))
  | 0, φ => by
    simp only [iidAvg, List.ofFn_zero]
    rw [avg_const ⟨Fin.elim0, Finset.mem_univ _⟩]
  | n + 1, φ => by
    have key : avg univ (fun v : Fin (n + 1) → ι => φ (List.ofFn v)) =
        avg univ (fun p : ι × (Fin n → ι) => φ (p.1 :: List.ofFn p.2)) := by
      rw [← avg_univ_equiv (Fin.consEquiv fun _ : Fin (n + 1) => ι)]
      refine avg_congr fun p _ => ?_
      simp [Fin.consEquiv, List.ofFn_succ]
    rw [key, avg_univ_prod]
    simp only [iidAvg]
    exact avg_congr fun i _ => iidAvg_ofFn n _

end iid

variable {S : Type} [Fintype S] [DecidableEq S]

/-- For a regular map, the image of a uniform state is uniform. -/
theorem avg_comp_regular [Nonempty S] {N : Type} [Fintype N] [DecidableEq N] (out : S → N)
    (F : ℕ) (hF : ∀ n : N, (univ.filter fun s => out s = n).card = F) (h : N → ℝ) :
    avg univ (fun s => h (out s)) = avg univ h := by
  have hS := card_eq_of_regular out F hF
  have hpos : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hF0 : (F : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hS
    linarith
  unfold avg
  rw [Finset.card_univ, Finset.card_univ, sum_comp_of_regular out F hF h, hS,
    mul_div_mul_left _ _ hF0]

theorem iidAvg_map [Nonempty S] {N : Type} [Fintype N] [DecidableEq N] (out : S → N) (F : ℕ)
    (hF : ∀ n : N, (univ.filter fun s => out s = n).card = F) :
    ∀ (n : ℕ) (φ : List N → ℝ), iidAvg S n (fun os => φ (os.map out)) = iidAvg N n φ
  | 0, _ => rfl
  | n + 1, φ => by
    simp only [iidAvg, List.map_cons]
    rw [← avg_comp_regular out F hF (fun i => iidAvg N n fun is => φ (i :: is))]
    exact avg_congr fun o _ => iidAvg_map out F hF n (fun ns => φ (out o :: ns))

/-! ### Tables with several ghost entries -/

namespace Trace

theorem mem_usedIn_perm_append {t t' : Trace S} {Γ : List (Entry S)} (hp : t'.Perm (Γ ++ t))
    {x : S} : x ∈ t'.usedIn ↔ (∃ g ∈ Γ, g.inp = x) ∨ x ∈ t.usedIn := by
  simp only [mem_usedIn, hp.mem_iff, List.mem_append]
  constructor
  · rintro ⟨e, he | he, rfl⟩
    · exact Or.inl ⟨e, he, rfl⟩
    · exact Or.inr ⟨e, he, rfl⟩
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact ⟨e, Or.inl he, rfl⟩
    · exact ⟨e, Or.inr he, rfl⟩

theorem mem_usedOut_perm_append {t t' : Trace S} {Γ : List (Entry S)} (hp : t'.Perm (Γ ++ t))
    {y : S} : y ∈ t'.usedOut ↔ (∃ g ∈ Γ, g.out = y) ∨ y ∈ t.usedOut := by
  simp only [mem_usedOut, hp.mem_iff, List.mem_append]
  constructor
  · rintro ⟨e, he | he, rfl⟩
    · exact Or.inl ⟨e, he, rfl⟩
    · exact Or.inr ⟨e, he, rfl⟩
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact ⟨e, Or.inl he, rfl⟩
    · exact ⟨e, Or.inr he, rfl⟩

theorem fwdHits_perm_append {t t' : Trace S} {Γ : List (Entry S)} (hp : t'.Perm (Γ ++ t))
    {x : S} (hx : ∀ g ∈ Γ, g.inp ≠ x) : t'.fwdHits x = t.fwdHits x := by
  ext y
  simp only [mem_fwdHits, hp.mem_iff, List.mem_append]
  constructor
  · rintro ⟨e, he | he, h1, h2⟩
    · exact absurd h1 (hx e he)
    · exact ⟨e, he, h1, h2⟩
  · rintro ⟨e, he, h1, h2⟩
    exact ⟨e, Or.inr he, h1, h2⟩

theorem invHits_perm_append {t t' : Trace S} {Γ : List (Entry S)} (hp : t'.Perm (Γ ++ t))
    {y : S} (hy : ∀ g ∈ Γ, g.out ≠ y) : t'.invHits y = t.invHits y := by
  ext x
  simp only [mem_invHits, hp.mem_iff, List.mem_append]
  constructor
  · rintro ⟨e, he | he, h1, h2⟩
    · exact absurd h1 (hy e he)
    · exact ⟨e, he, h1, h2⟩
  · rintro ⟨e, he, h1, h2⟩
    exact ⟨e, Or.inr he, h1, h2⟩

theorem WF.of_perm_append {t t' : Trace S} {Γ : List (Entry S)} (hp : t'.Perm (Γ ++ t))
    (h : WF t') : WF t := by
  have h1 := (hp.map Entry.inp).nodup_iff.1 h.inp
  have h2 := (hp.map Entry.out).nodup_iff.1 h.out
  rw [List.map_append] at h1 h2
  exact ⟨h1.of_append_right, h2.of_append_right⟩

end Trace

namespace Strat

variable {α : Type}

/-- The table touches one of the ghost entries `Γ`. -/
def TouchedAny (Γ : List (Entry S)) (t : Trace S) : Prop := ∃ g ∈ Γ, Touched g t

theorem TouchedAny.mono {Γ : List (Entry S)} {t t' : Trace S} (h : t <:+ t')
    (ht : TouchedAny Γ t) : TouchedAny Γ t' := by
  obtain ⟨g, hg, hT⟩ := ht
  exact ⟨g, hg, hT.mono h⟩

theorem exp_untouchedAny_zero (Γ : List (Entry S)) (f : α → ℝ) (st : Strat S α) (s : PState S)
    (h : TouchedAny Γ s.trace) :
    st.exp s (fun a s' => ind (¬ TouchedAny Γ s'.trace) * f a) = 0 := by
  rw [exp_congr_of_post (post_suffix st s) (g := fun _ _ => 0), exp_zero]
  intro a s' hs
  rw [ind_neg (not_not.2 (h.mono hs)), zero_mul]

/-- One-sided ghost lemma for several entries: the part of the expectation from `t` on runs that
touch none of `Γ` is at most the expectation from the table `t'` that contains `Γ`. -/
theorem exp_ghosts_le (Γ : List (Entry S)) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (st : Strat S α)
    (t t' : Trace S) (c c' : ℕ) (hp : t'.Perm (Γ ++ t)) (hwf' : t'.WF) :
    st.exp ⟨t, c⟩ (fun a s' => ind (¬ TouchedAny Γ s'.trace) * f a) ≤
      st.exp ⟨t', c'⟩ (fun a _ => f a) := by
  induction st generalizing t t' c c' with
  | done a => exact mul_le_of_le_one_left (hf a) (ind_le_one _)
  | rand n k ih => exact avg_mono fun i _ => ih i t t' c c' hp hwf'
  | fwd x k ih =>
    simp only [Strat.exp]
    by_cases hxg : ∃ g ∈ Γ, g.inp = x
    · have hz : ∀ y ∈ t.fwdAns x, (k y).exp ⟨t.stepF x y, c + 1⟩
          (fun a s' => ind (¬ TouchedAny Γ s'.trace) * f a) = 0 := fun y _ => by
        obtain ⟨g, hg, hgx⟩ := hxg
        exact exp_untouchedAny_zero Γ f (k y) _
          ⟨g, hg, Or.inl (by rw [hgx]; exact Trace.mem_usedIn_stepF t x y)⟩
      rw [avg_congr hz, avg_zero]
      exact avg_nonneg fun y _ => exp_nonneg (fun a _ => hf a) _ _
    · push_neg at hxg
      by_cases hx : x ∈ t.usedIn
      · have hx' : x ∈ t'.usedIn := (Trace.mem_usedIn_perm_append hp).2 (Or.inr hx)
        have e1 : t.fwdAns x = t.fwdHits x := if_pos hx
        have e2 : t'.fwdAns x = t.fwdHits x :=
          (if_pos hx').trans (Trace.fwdHits_perm_append hp hxg)
        have e3 : ∀ y, t.stepF x y = t := fun y => if_pos hx
        have e4 : ∀ y, t'.stepF x y = t' := fun y => if_pos hx'
        simp only [e1, e2, e3, e4]
        exact avg_mono fun y _ => ih y t t' _ _ hp hwf'
      · have hx' : x ∉ t'.usedIn := fun h =>
          ((Trace.mem_usedIn_perm_append hp).1 h).elim
            (fun ⟨g, hg, hgx⟩ => hxg g hg hgx) hx
        have e1 : t.fwdAns x = t.freeOut := if_neg hx
        have e2 : t'.fwdAns x = t'.freeOut := if_neg hx'
        have e3 : ∀ y, t.stepF x y = ⟨.fwd, x, y⟩ :: t := fun y => if_neg hx
        have e4 : ∀ y, t'.stepF x y = ⟨.fwd, x, y⟩ :: t' := fun y => if_neg hx'
        simp only [e1, e2, e3, e4]
        have hsub : t'.freeOut ⊆ t.freeOut := fun y hy => by
          rw [Trace.mem_freeOut] at hy ⊢
          exact fun h => hy ((Trace.mem_usedOut_perm_append hp).2 (Or.inr h))
        refine avg_le_avg_of_subset hsub ?_ ?_ ?_
        · intro y hy hny
          have hyu : y ∈ t'.usedOut := by
            by_contra h
            exact hny (Trace.mem_freeOut.2 h)
          rcases (Trace.mem_usedOut_perm_append hp).1 hyu with ⟨g, hg, hgy⟩ | h
          · exact (exp_untouchedAny_zero Γ f (k y) _ ⟨g, hg, Or.inr
              (Trace.mem_usedOut.2 ⟨⟨.fwd, x, y⟩, List.mem_cons_self, hgy.symm⟩)⟩).le
          · exact absurd h (Trace.mem_freeOut.1 hy)
        · intro y hy
          exact ih y _ _ _ _ ((hp.cons _).trans List.perm_middle.symm)
            (hwf'.cons hx' (Trace.mem_freeOut.1 hy))
        · intro y _
          exact exp_nonneg (fun a _ => hf a) _ _
  | inv y k ih =>
    simp only [Strat.exp]
    by_cases hyg : ∃ g ∈ Γ, g.out = y
    · have hz : ∀ x ∈ t.invAns y, (k x).exp ⟨t.stepI x y, c + 1⟩
          (fun a s' => ind (¬ TouchedAny Γ s'.trace) * f a) = 0 := fun x _ => by
        obtain ⟨g, hg, hgy⟩ := hyg
        exact exp_untouchedAny_zero Γ f (k x) _
          ⟨g, hg, Or.inr (by rw [hgy]; exact Trace.mem_usedOut_stepI t x y)⟩
      rw [avg_congr hz, avg_zero]
      exact avg_nonneg fun x _ => exp_nonneg (fun a _ => hf a) _ _
    · push_neg at hyg
      by_cases hy : y ∈ t.usedOut
      · have hy' : y ∈ t'.usedOut := (Trace.mem_usedOut_perm_append hp).2 (Or.inr hy)
        have e1 : t.invAns y = t.invHits y := if_pos hy
        have e2 : t'.invAns y = t.invHits y :=
          (if_pos hy').trans (Trace.invHits_perm_append hp hyg)
        have e3 : ∀ x, t.stepI x y = t := fun x => if_pos hy
        have e4 : ∀ x, t'.stepI x y = t' := fun x => if_pos hy'
        simp only [e1, e2, e3, e4]
        exact avg_mono fun x _ => ih x t t' _ _ hp hwf'
      · have hy' : y ∉ t'.usedOut := fun h =>
          ((Trace.mem_usedOut_perm_append hp).1 h).elim
            (fun ⟨g, hg, hgy⟩ => hyg g hg hgy) hy
        have e1 : t.invAns y = t.freeIn := if_neg hy
        have e2 : t'.invAns y = t'.freeIn := if_neg hy'
        have e3 : ∀ x, t.stepI x y = ⟨.inv, x, y⟩ :: t := fun x => if_neg hy
        have e4 : ∀ x, t'.stepI x y = ⟨.inv, x, y⟩ :: t' := fun x => if_neg hy'
        simp only [e1, e2, e3, e4]
        have hsub : t'.freeIn ⊆ t.freeIn := fun x hx => by
          rw [Trace.mem_freeIn] at hx ⊢
          exact fun h => hx ((Trace.mem_usedIn_perm_append hp).2 (Or.inr h))
        refine avg_le_avg_of_subset hsub ?_ ?_ ?_
        · intro x hx hnx
          have hxu : x ∈ t'.usedIn := by
            by_contra h
            exact hnx (Trace.mem_freeIn.2 h)
          rcases (Trace.mem_usedIn_perm_append hp).1 hxu with ⟨g, hg, hgx⟩ | h
          · exact (exp_untouchedAny_zero Γ f (k x) _ ⟨g, hg, Or.inl
              (Trace.mem_usedIn.2 ⟨⟨.inv, x, y⟩, List.mem_cons_self, hgx.symm⟩)⟩).le
          · exact absurd h (Trace.mem_freeIn.1 hx)
        · intro x hx
          exact ih x _ _ _ _ ((hp.cons _).trans List.perm_middle.symm)
            (hwf'.cons (Trace.mem_freeIn.1 hx) hy')
        · intro x _
          exact exp_nonneg (fun a _ => hf a) _ _

/-- **Ghost lemma for several entries.** If `t'` is `t` plus the entries `Γ`, the expectations
of a `[0, 1]`-valued function of the result from `t'` and from `t` differ by at most the
probability that the run from `t` touches one of them. -/
theorem abs_exp_ghosts_le (Γ : List (Entry S)) (f : α → ℝ) (hf0 : ∀ a, 0 ≤ f a)
    (hf1 : ∀ a, f a ≤ 1) (st : Strat S α) (t t' : Trace S) (c c' : ℕ) (hp : t'.Perm (Γ ++ t))
    (hwf' : t'.WF) :
    |st.exp ⟨t', c'⟩ (fun a _ => f a) - st.exp ⟨t, c⟩ (fun a _ => f a)| ≤
      st.exp ⟨t, c⟩ (fun _ s' => ind (TouchedAny Γ s'.trace)) := by
  have hwf : t.WF := Trace.WF.of_perm_append hp hwf'
  have key : ∀ f' : α → ℝ, (∀ a, 0 ≤ f' a) → (∀ a, f' a ≤ 1) →
      st.exp ⟨t, c⟩ (fun a _ => f' a) ≤ st.exp ⟨t', c'⟩ (fun a _ => f' a) +
        st.exp ⟨t, c⟩ (fun _ s' => ind (TouchedAny Γ s'.trace)) := by
    intro f' h0 h1
    have hpt : ∀ (a : α) (s' : PState S),
        f' a ≤ ind (¬ TouchedAny Γ s'.trace) * f' a + ind (TouchedAny Γ s'.trace) := by
      intro a s'
      by_cases hT : TouchedAny Γ s'.trace
      · rw [ind_pos hT, ind_neg (not_not.2 hT)]
        linarith [h1 a]
      · rw [ind_neg hT, ind_pos hT]
        linarith
    calc st.exp ⟨t, c⟩ (fun a _ => f' a)
        ≤ st.exp ⟨t, c⟩
            (fun a s' => ind (¬ TouchedAny Γ s'.trace) * f' a + ind (TouchedAny Γ s'.trace)) :=
          exp_mono hpt st _
      _ = st.exp ⟨t, c⟩ (fun a s' => ind (¬ TouchedAny Γ s'.trace) * f' a) +
            st.exp ⟨t, c⟩ (fun _ s' => ind (TouchedAny Γ s'.trace)) := exp_add _ _ st _
      _ ≤ _ := add_le_add (exp_ghosts_le Γ f' h0 st t t' c c' hp hwf') (le_refl _)
  have k1 := key f hf0 hf1
  have k2 := key (fun a => 1 - f a) (fun a => by linarith [hf1 a]) (fun a => by linarith [hf0 a])
  have e1 : st.exp ⟨t, c⟩ (fun a _ => 1 - f a) = 1 - st.exp ⟨t, c⟩ (fun a _ => f a) :=
    exp_one_sub (f := fun a _ => f a) st ⟨t, c⟩ hwf
  have e2 : st.exp ⟨t', c'⟩ (fun a _ => 1 - f a) = 1 - st.exp ⟨t', c'⟩ (fun a _ => f a) :=
    exp_one_sub (f := fun a _ => f a) st ⟨t', c'⟩ hwf'
  rw [e1, e2] at k2
  rw [abs_le]
  constructor <;> linarith

/-- Expectations of two functions that are within `h` of each other on everything reachable are
within the expectation of `h`. -/
theorem abs_exp_sub_le_exp {P : α → PState S → Prop} {f g h : α → PState S → ℝ}
    {st : Strat S α} {s : PState S} (hP : st.post s P)
    (hfg : ∀ a s', P a s' → |f a s' - g a s'| ≤ h a s') :
    |st.exp s f - st.exp s g| ≤ st.exp s h := by
  have h1 : st.exp s f ≤ st.exp s g + st.exp s h := by
    rw [← exp_add]
    exact exp_le_exp_of_post hP fun a s' hp => by linarith [(abs_le.1 (hfg a s' hp)).2]
  have h2 : st.exp s g ≤ st.exp s f + st.exp s h := by
    rw [← exp_add]
    exact exp_le_exp_of_post hP fun a s' hp => by linarith [(abs_le.1 (hfg a s' hp)).1]
  rw [abs_le]
  constructor <;> linarith

/-! ### Touch counts -/

/-- The probability that the run ends with one of the states `os` among the used outputs. -/
noncomputable def touchAny (A : Strat S α) (s : PState S) (os : List S) : ℝ :=
  A.exp s fun _ s' => ind (∃ o ∈ os, o ∈ s'.trace.usedOut)

theorem post_usedOut_card {A : Strat S α} {q : ℕ} (hA : A.QB q) (s : PState S)
    (hs : s.trace.WF) :
    A.post s fun _ s' => s'.trace.usedOut.card ≤ s.trace.length + q :=
  post_mono (fun _ s' hp => by rw [hp.1.card_usedOut]; exact hp.2.2) (post_run hA s hs)

/-- Averaged over an injective family of points (here: the generator inputs of all seeds), the
probability that a run makes the point a new input is at most `q / |R|`. -/
theorem avg_sum_touchIn_le {R K : Type} [Fintype R] (enc : R × K → S)
    (henc : Function.Injective enc) (I : Finset K) {A : Strat S α} {q : ℕ} (hA : A.QB q)
    (s : PState S) (hs : s.trace.WF) :
    avg univ (fun r : R => ∑ k ∈ I, touchIn A s (enc (r, k))) ≤ (q : ℝ) / Fintype.card R := by
  unfold avg
  rw [Finset.card_univ]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  calc ∑ r : R, ∑ k ∈ I, touchIn A s (enc (r, k))
      = ∑ p ∈ (univ : Finset R) ×ˢ I, touchIn A s (enc p) :=
        (Finset.sum_product (univ : Finset R) I (fun p => touchIn A s (enc p))).symm
    _ = A.exp s (fun _ s' => ∑ p ∈ (univ : Finset R) ×ˢ I,
          ind (enc p ∈ s'.trace.usedIn ∧ enc p ∉ s.trace.usedIn)) := by
        unfold touchIn
        rw [← exp_sum]
    _ ≤ q := exp_le_of_post hs (post_run hA s hs) fun _ s' hp =>
        (sum_ind_le_of_injective _ (s'.trace.usedIn \ s.trace.usedIn) _ enc henc
          fun p _ h => Finset.mem_sdiff.2 h).trans
          (by exact_mod_cast card_new_in_le hs hp.1 hp.2.1 q hp.2.2)

/-- Seeds whose generator inputs meet the table: at most `|T|` of them. -/
theorem avg_bad_le {R K : Type} [Fintype R] (enc : R × K → S) (henc : Function.Injective enc)
    (I : Finset K) (T : Trace S) (hT : T.WF) :
    avg univ (fun r : R => ind (∃ k ∈ I, enc (r, k) ∈ T.usedIn)) ≤
      (T.length : ℝ) / Fintype.card R := by
  unfold avg
  rw [Finset.card_univ]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  calc ∑ r : R, ind (∃ k ∈ I, enc (r, k) ∈ T.usedIn)
      ≤ ∑ r : R, ∑ k ∈ I, ind (enc (r, k) ∈ T.usedIn) :=
        Finset.sum_le_sum fun r _ => ind_exists_le_sum I _
    _ = ∑ p ∈ (univ : Finset R) ×ˢ I, ind (enc p ∈ T.usedIn) :=
        (Finset.sum_product (univ : Finset R) I (fun p => ind (enc p ∈ T.usedIn))).symm
    _ ≤ (T.usedIn.card : ℝ) := sum_ind_le_of_injective _ _ _ enc henc fun p _ h => h
    _ = T.length := by rw [hT.card_usedIn]

/-- A run that uses at most `M` outputs hits a uniform state, handed to it through its regular
part `out`, with probability at most `M / F`. -/
theorem avg_touchOut_fiber_le {N : Type} [Fintype N] [DecidableEq N] [Nonempty N] (out : S → N)
    (F : ℕ) (hF : ∀ n : N, (univ.filter fun s => out s = n).card = F) (C : N → Strat S α)
    (s : PState S) (hs : s.trace.WF) (M : ℕ)
    (hC : ∀ n, (C n).post s fun _ s' => s'.trace.usedOut.card ≤ M) :
    avg univ (fun o : S => touchOut (C (out o)) s o) ≤ (M : ℝ) / F := by
  have hS := card_eq_of_regular out F hF
  have hN : (0 : ℝ) < Fintype.card N := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ o : S, touchOut (C (out o)) s o ≤ (Fintype.card N : ℝ) * M := by
    rw [← Finset.sum_fiberwise univ out (fun o => touchOut (C (out o)) s o)]
    have hfib : ∀ n ∈ (univ : Finset N),
        ∑ o ∈ univ.filter (fun o => out o = n), touchOut (C (out o)) s o ≤ (M : ℝ) := by
      intro n _
      have hc : ∀ o ∈ univ.filter (fun o => out o = n),
          touchOut (C (out o)) s o = touchOut (C n) s o := fun o ho => by
        rw [(Finset.mem_filter.1 ho).2]
      rw [Finset.sum_congr rfl hc]
      unfold touchOut
      rw [← exp_sum]
      exact exp_le_of_post hs (hC n) fun _ s' hM =>
        (sum_ind_le _ s'.trace.usedOut _ fun o _ ho => ho).trans (by exact_mod_cast hM)
    refine (Finset.sum_le_sum hfib).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold avg
  rw [Finset.card_univ, hS]
  calc (∑ o : S, touchOut (C (out o)) s o) / ((F : ℝ) * Fintype.card N)
      ≤ ((Fintype.card N : ℝ) * M) / ((F : ℝ) * Fintype.card N) :=
        div_le_div_of_nonneg_right hsum (by positivity)
    _ = (M : ℝ) / F := by rw [mul_comm (F : ℝ), mul_div_mul_left _ _ hN.ne']

/-- With independent uniform states handed to the run through their parts, the run hits one of
them with probability at most `L M / F`. -/
theorem iidAvg_touchAny_le {N : Type} [Fintype N] [DecidableEq N] [Nonempty N] (out : S → N)
    (F : ℕ) (hF : ∀ n : N, (univ.filter fun s => out s = n).card = F) (T : Trace S) (c : ℕ)
    (hT : T.WF) (M : ℕ) : ∀ (L : ℕ) (B : List N → Strat S α),
      (∀ ns, (B ns).post ⟨T, c⟩ fun _ s' => s'.trace.usedOut.card ≤ M) →
      iidAvg S L (fun os => touchAny (B (os.map out)) ⟨T, c⟩ os) ≤ (L : ℝ) * M / F
  | 0, B, _ => by
    have h0 : touchAny (B (([] : List S).map out)) ⟨T, c⟩ [] = 0 := by
      unfold touchAny
      rw [exp_congr_of_post (post_suffix (B (([] : List S).map out)) ⟨T, c⟩)
        (g := fun _ _ => 0), exp_zero]
      intro _ s' _
      exact ind_neg (by simp)
    show touchAny (B (([] : List S).map out)) ⟨T, c⟩ [] ≤ _
    rw [h0]
    simp
  | L + 1, B, hB => by
    have hstep : ∀ (o : S) (os : List S), touchAny (B ((o :: os).map out)) ⟨T, c⟩ (o :: os) ≤
        touchOut (B (out o :: os.map out)) ⟨T, c⟩ o +
          touchAny (B (out o :: os.map out)) ⟨T, c⟩ os := by
      intro o os
      unfold touchAny touchOut
      rw [List.map_cons, ← exp_add]
      refine exp_mono (fun _ s' => ?_) _ _
      by_cases h1 : o ∈ s'.trace.usedOut
      · rw [ind_pos h1]
        linarith [ind_le_one (∃ o' ∈ o :: os, o' ∈ s'.trace.usedOut),
          ind_nonneg (∃ o' ∈ os, o' ∈ s'.trace.usedOut)]
      · rw [ind_neg h1, zero_add]
        refine ind_mono ?_
        rintro ⟨o', ho', hu⟩
        rcases List.mem_cons.1 ho' with rfl | ho'
        · exact absurd hu h1
        · exact ⟨o', ho', hu⟩
    have IH : ∀ o : S, iidAvg S L (fun os => touchAny (B (out o :: os.map out)) ⟨T, c⟩ os) ≤
        (L : ℝ) * M / F := fun o =>
      iidAvg_touchAny_le out F hF T c hT M L (fun ns => B (out o :: ns)) (fun ns => hB _)
    have hfirst : avg univ (fun o : S =>
        iidAvg S L (fun os => touchOut (B (out o :: os.map out)) ⟨T, c⟩ o)) ≤ (M : ℝ) / F := by
      rw [iidAvg_avg]
      exact iidAvg_le (by positivity) fun os =>
        avg_touchOut_fiber_le out F hF (fun n => B (n :: os.map out)) ⟨T, c⟩ hT M (fun n => hB _)
    show avg univ (fun o : S => iidAvg S L
        (fun os => touchAny (B ((o :: os).map out)) ⟨T, c⟩ (o :: os))) ≤ _
    calc avg univ (fun o : S => iidAvg S L
          (fun os => touchAny (B ((o :: os).map out)) ⟨T, c⟩ (o :: os)))
        ≤ avg univ (fun o : S =>
            iidAvg S L (fun os => touchOut (B (out o :: os.map out)) ⟨T, c⟩ o) +
              iidAvg S L (fun os => touchAny (B (out o :: os.map out)) ⟨T, c⟩ os)) :=
          avg_mono fun o _ => by
            rw [← iidAvg_add]
            exact iidAvg_mono fun os => hstep o os
      _ = avg univ (fun o : S =>
            iidAvg S L (fun os => touchOut (B (out o :: os.map out)) ⟨T, c⟩ o)) +
          avg univ (fun o : S =>
            iidAvg S L (fun os => touchAny (B (out o :: os.map out)) ⟨T, c⟩ os)) := avg_add
      _ ≤ (M : ℝ) / F + (L : ℝ) * M / F :=
          add_le_add hfirst (avg_le (by positivity) fun o _ => IH o)
      _ = ((L + 1 : ℕ) : ℝ) * M / F := by push_cast; ring

end Strat

/-! ### The generator -/

variable {R K N : Type}

/-- A counter-mode generator: block `k` under seed `r` is `out (π (enc (r, k)))`. -/
structure GenCall (S R K N : Type) where
  enc : R × K → S
  enc_inj : Function.Injective enc
  out : S → N

namespace GenCall
variable (G : GenCall S R K N)

/-- Query the blocks of the counters in order and return their revealed parts. -/
def blocks (seed : R) : List K → Strat S (List N)
  | [] => .done []
  | k :: ks => .fwd (G.enc (seed, k)) fun o => (blocks seed ks).bind fun ns => .done (G.out o :: ns)

/-- Real: first stage, uniform seed, the blocks, second stage on the revealed parts. -/
noncomputable def genReal [Fintype R] [Nonempty R] {σ : Type} (ks : List K)
    (A1 : Strat S σ) (A2 : σ → List N → Strat S Bool) : Strat S Bool :=
  A1.bind fun a => Strat.uniform R fun seed => (G.blocks seed ks).bind (A2 a)

/-- Ideal: the revealed parts are independent uniform values and no generator query is made.
(The generator is an explicit argument, unused, so that `G.genIdeal` resolves.) -/
noncomputable def genIdeal (_G : GenCall S R K N) [Fintype N] [Nonempty N] {σ : Type} (count : ℕ)
    (A1 : Strat S σ) (A2 : σ → List N → Strat S Bool) : Strat S Bool :=
  A1.bind fun a => Strat.uniform (Fin count → N) fun ns => A2 a (List.ofFn ns)

/-- The same queries as `blocks`, returning the whole replies. -/
def replies (seed : R) : List K → Strat S (List S)
  | [] => .done []
  | k :: ks => .fwd (G.enc (seed, k)) fun o => (replies seed ks).bind fun os => .done (o :: os)

/-- The table entries the generator queries add, for the replies `os`. -/
def ghosts (seed : R) (ks : List K) (os : List S) : List (Entry S) :=
  (ks.zip os).map fun p => ⟨.fwd, G.enc (seed, p.1), p.2⟩

theorem exp_blocks (seed : R) : ∀ (ks : List K) (s : PState S) (f : List N → PState S → ℝ),
    (G.blocks seed ks).exp s f = (G.replies seed ks).exp s (fun os s' => f (os.map G.out) s')
  | [], _, _ => rfl
  | k :: ks, s, f => by
    simp only [blocks, replies, Strat.exp, Strat.exp_bind]
    refine avg_congr fun o _ => ?_
    rw [exp_blocks seed ks]
    rfl

theorem exp_replies_cons (seed : R) (k : K) (ks : List K) (T : Trace S) (c : ℕ)
    (hx : G.enc (seed, k) ∉ T.usedIn) (f : List S → PState S → ℝ) :
    (G.replies seed (k :: ks)).exp ⟨T, c⟩ f =
      avg T.freeOut fun y => (G.replies seed ks).exp ⟨⟨.fwd, G.enc (seed, k), y⟩ :: T, c + 1⟩
        fun os s' => f (y :: os) s' := by
  have e1 : T.fwdAns (G.enc (seed, k)) = T.freeOut := if_neg hx
  have e3 : ∀ y, T.stepF (G.enc (seed, k)) y = ⟨.fwd, G.enc (seed, k), y⟩ :: T :=
    fun y => if_neg hx
  simp only [replies, Strat.exp, Strat.exp_bind, e1, e3]

theorem fresh_cons (seed : R) {k : K} {ks : List K} (hks : (k :: ks).Nodup) {T : Trace S}
    (hfresh : ∀ k' ∈ k :: ks, G.enc (seed, k') ∉ T.usedIn) (y : S) :
    ∀ k' ∈ ks, G.enc (seed, k') ∉ Trace.usedIn (⟨.fwd, G.enc (seed, k), y⟩ :: T) := by
  intro k' hk' hmem
  obtain ⟨e, he, hex⟩ := Trace.mem_usedIn.1 hmem
  rcases List.mem_cons.1 he with rfl | he
  · have h := G.enc_inj hex
    simp only [Prod.mk.injEq] at h
    exact (List.nodup_cons.1 hks).1 (by rw [h.2]; exact hk')
  · exact hfresh k' (List.mem_cons_of_mem _ hk') (Trace.mem_usedIn.2 ⟨e, he, hex⟩)

/-- For a seed whose generator inputs are fresh, every run of the generator ends with the table
`T` plus the ghost entries of its replies. -/
theorem post_replies (seed : R) : ∀ (ks : List K) (T : Trace S) (c : ℕ), ks.Nodup → T.WF →
    (∀ k ∈ ks, G.enc (seed, k) ∉ T.usedIn) →
    (G.replies seed ks).post ⟨T, c⟩ fun os s' =>
      s'.trace.Perm (G.ghosts seed ks os ++ T) ∧ s'.trace.WF
  | [], _, _, _, hT, _ => ⟨List.Perm.refl _, hT⟩
  | k :: ks, T, c, hks, hT, hfresh => by
    have hx : G.enc (seed, k) ∉ T.usedIn := hfresh k List.mem_cons_self
    intro y hy
    have e1 : T.fwdAns (G.enc (seed, k)) = T.freeOut := if_neg hx
    have e3 : T.stepF (G.enc (seed, k)) y = ⟨.fwd, G.enc (seed, k), y⟩ :: T := if_neg hx
    rw [e1] at hy
    show ((G.replies seed ks).bind fun os => Strat.done (y :: os)).post
      ⟨T.stepF (G.enc (seed, k)) y, c + 1⟩ _
    rw [e3]
    apply Strat.post_bind
    have hT' : Trace.WF (⟨.fwd, G.enc (seed, k), y⟩ :: T) := hT.cons hx (Trace.mem_freeOut.1 hy)
    refine Strat.post_mono ?_ (post_replies seed ks _ (c + 1) (List.nodup_cons.1 hks).2 hT'
      (G.fresh_cons seed hks hfresh y))
    rintro os s' ⟨hp, hwf⟩
    exact ⟨hp.trans List.perm_middle, hwf⟩

/-- The replies of fresh generator queries, as a list, are within `L (|T| + L) / |S|` of
independent uniform states. -/
theorem abs_exp_replies_sub_le (seed : R) : ∀ (ks : List K) (T : Trace S) (c : ℕ), ks.Nodup →
    T.WF → (∀ k ∈ ks, G.enc (seed, k) ∉ T.usedIn) → ∀ (φ : List S → ℝ), (∀ os, 0 ≤ φ os) →
    (∀ os, φ os ≤ 1) →
    |(G.replies seed ks).exp ⟨T, c⟩ (fun os _ => φ os) - iidAvg S ks.length φ| ≤
      (ks.length : ℝ) * (T.length + ks.length) / Fintype.card S
  | [], _, _, _, _, _, _, _, _ => by simp [replies, iidAvg, Strat.exp]
  | k :: ks, T, c, hks, hT, hfresh, φ, h0, h1 => by
    have hx : G.enc (seed, k) ∉ T.usedIn := hfresh k List.mem_cons_self
    have hlt : T.length < Fintype.card S := hT.length_lt_of_not_mem_usedIn hx
    have hS : (0 : ℝ) < Fintype.card S := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hlt
    rw [G.exp_replies_cons seed k ks T c hx]
    simp only [iidAvg, List.length_cons]
    have hY0 : ∀ o, 0 ≤ iidAvg S ks.length (fun os => φ (o :: os)) :=
      fun o => iidAvg_nonneg fun _ => h0 _
    have hY1 : ∀ o, iidAvg S ks.length (fun os => φ (o :: os)) ≤ 1 :=
      fun o => iidAvg_le zero_le_one fun _ => h1 _
    have hIH : ∀ y ∈ T.freeOut,
        |(G.replies seed ks).exp ⟨⟨.fwd, G.enc (seed, k), y⟩ :: T, c + 1⟩
            (fun os _ => φ (y :: os)) - iidAvg S ks.length (fun os => φ (y :: os))| ≤
          (ks.length : ℝ) * ((T.length : ℝ) + 1 + ks.length) / Fintype.card S := by
      intro y hy
      have hT' : Trace.WF (⟨.fwd, G.enc (seed, k), y⟩ :: T) :=
        hT.cons hx (Trace.mem_freeOut.1 hy)
      have h := abs_exp_replies_sub_le seed ks _ (c + 1) (List.nodup_cons.1 hks).2 hT'
        (G.fresh_cons seed hks hfresh y) (fun os => φ (y :: os)) (fun _ => h0 _) (fun _ => h1 _)
      simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using h
    have hA : |avg T.freeOut (fun y => (G.replies seed ks).exp
          ⟨⟨.fwd, G.enc (seed, k), y⟩ :: T, c + 1⟩ (fun os _ => φ (y :: os))) -
        avg T.freeOut (fun y => iidAvg S ks.length (fun os => φ (y :: os)))| ≤
        (ks.length : ℝ) * ((T.length : ℝ) + 1 + ks.length) / Fintype.card S :=
      (abs_avg_sub_le _ _ _).trans (avg_le (by positivity) hIH)
    have hB : |avg T.freeOut (fun y => iidAvg S ks.length (fun os => φ (y :: os))) -
        avg univ (fun y => iidAvg S ks.length (fun os => φ (y :: os)))| ≤
        (T.length : ℝ) / Fintype.card S :=
      abs_avg_free_sub_avg_univ (D := S) id 1 (fun d => by
          have hd : (univ.filter fun s : S => id s = d) = {d} := by
            ext s
            simp
          rw [hd, Finset.card_singleton]) T hT hlt
        (fun y => iidAvg S ks.length (fun os => φ (y :: os))) hY0 hY1
    refine (abs_sub_le _ (avg T.freeOut (fun y => iidAvg S ks.length (fun os => φ (y :: os))))
      _).trans ((add_le_add hA hB).trans ?_)
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ hS.le
    push_cast
    have ht : (0 : ℝ) ≤ T.length := Nat.cast_nonneg _
    have hl : (0 : ℝ) ≤ ks.length := Nat.cast_nonneg _
    nlinarith

theorem ind_touchedAny_le [DecidableEq K] (seed : R) (ks : List K) (T : Trace S) (os : List S)
    (t : Trace S) (hfresh : ∀ k ∈ ks, G.enc (seed, k) ∉ T.usedIn) :
    ind (Strat.TouchedAny (G.ghosts seed ks os) t) ≤
      ∑ k ∈ ks.toFinset, ind (G.enc (seed, k) ∈ t.usedIn ∧ G.enc (seed, k) ∉ T.usedIn) +
        ind (∃ o ∈ os, o ∈ t.usedOut) := by
  have hn0 : 0 ≤ ∑ k ∈ ks.toFinset, ind (G.enc (seed, k) ∈ t.usedIn ∧ G.enc (seed, k) ∉ T.usedIn) :=
    Finset.sum_nonneg fun _ _ => ind_nonneg _
  have hn1 := ind_nonneg (∃ o ∈ os, o ∈ t.usedOut)
  by_cases hT : Strat.TouchedAny (G.ghosts seed ks os) t
  · rw [ind_pos hT]
    obtain ⟨g, hg, hTg⟩ := hT
    obtain ⟨⟨k, o⟩, hp, rfl⟩ := List.mem_map.1 hg
    have hmem := List.of_mem_zip hp
    rcases hTg with h | h
    · have hk : G.enc (seed, k) ∈ t.usedIn ∧ G.enc (seed, k) ∉ T.usedIn := ⟨h, hfresh k hmem.1⟩
      have h1 : ind (G.enc (seed, k) ∈ t.usedIn ∧ G.enc (seed, k) ∉ T.usedIn) ≤
          ∑ k ∈ ks.toFinset, ind (G.enc (seed, k) ∈ t.usedIn ∧ G.enc (seed, k) ∉ T.usedIn) :=
        Finset.single_le_sum (f := fun k => ind (G.enc (seed, k) ∈ t.usedIn ∧
          G.enc (seed, k) ∉ T.usedIn)) (fun _ _ => ind_nonneg _) (List.mem_toFinset.2 hmem.1)
      rw [ind_pos hk] at h1
      linarith
    · have h2 : ind (∃ o' ∈ os, o' ∈ t.usedOut) = 1 := ind_pos ⟨o, hmem.2, h⟩
      linarith
  · rw [ind_neg hT]
    linarith

theorem touch_ghosts_le [DecidableEq K] {α : Type} (seed : R) (ks : List K) (T : Trace S) (c : ℕ)
    (os : List S) (A : Strat S α) (hfresh : ∀ k ∈ ks, G.enc (seed, k) ∉ T.usedIn) :
    A.exp ⟨T, c⟩ (fun _ s' => ind (Strat.TouchedAny (G.ghosts seed ks os) s'.trace)) ≤
      ∑ k ∈ ks.toFinset, Strat.touchIn A ⟨T, c⟩ (G.enc (seed, k)) +
        Strat.touchAny A ⟨T, c⟩ os := by
  unfold Strat.touchIn Strat.touchAny
  rw [← Strat.exp_sum, ← Strat.exp_add]
  exact Strat.exp_mono (fun _ s' => G.ind_touchedAny_le seed ks T os s'.trace hfresh) _ _

/-- The bound from a table `T` reached by the first stage, for a nonempty state space. -/
theorem gen_core_ne [Nonempty S] [Fintype R] [Nonempty R] [Fintype N] [Nonempty N]
    [DecidableEq N] [DecidableEq K]
    (F : ℕ) (hF : ∀ n : N, (univ.filter fun s => G.out s = n).card = F)
    (ks : List K) (hks : ks.Nodup) (B : List N → Strat S Bool) (q2 : ℕ)
    (hB : ∀ ns, (B ns).QB q2) (T : Trace S) (c : ℕ) (hT : T.WF) :
    |avg univ (fun r : R => (G.replies r ks).exp ⟨T, c⟩
          fun os s' => Strat.acc (B (os.map G.out)) s') -
        iidAvg N ks.length (fun ns => Strat.acc (B ns) ⟨T, c⟩)| ≤
      ((T.length : ℝ) + q2) / Fintype.card R + (ks.length : ℝ) * (T.length + q2) / F +
        2 * ((ks.length : ℝ) * (T.length + ks.length) / Fintype.card S) := by
  have hE0 : 0 ≤ (ks.length : ℝ) * (T.length + ks.length) / Fintype.card S := by positivity
  have hideal : iidAvg N ks.length (fun ns => Strat.acc (B ns) ⟨T, c⟩) =
      iidAvg S ks.length (fun os => Strat.acc (B (os.map G.out)) ⟨T, c⟩) :=
    (iidAvg_map G.out F hF _ _).symm
  have hI0 : 0 ≤ iidAvg N ks.length (fun ns => Strat.acc (B ns) ⟨T, c⟩) :=
    iidAvg_nonneg fun _ => Strat.acc_nonneg _ _
  have hI1 : iidAvg N ks.length (fun ns => Strat.acc (B ns) ⟨T, c⟩) ≤ 1 :=
    iidAvg_le zero_le_one fun _ => Strat.acc_le_one _ _
  have hΨ0 : ∀ (r : R) (os : List S), 0 ≤ ∑ k ∈ ks.toFinset,
      Strat.touchIn (B (os.map G.out)) ⟨T, c⟩ (G.enc (r, k)) :=
    fun r os => Finset.sum_nonneg fun k _ => Strat.touchIn_nonneg _ _ _
  have hΘ0 : ∀ os : List S, 0 ≤ Strat.touchAny (B (os.map G.out)) ⟨T, c⟩ os :=
    fun os => Strat.exp_nonneg (fun _ _ => ind_nonneg _) _ _
  have per_seed : ∀ r : R,
      |(G.replies r ks).exp ⟨T, c⟩ (fun os s' => Strat.acc (B (os.map G.out)) s') -
          iidAvg N ks.length (fun ns => Strat.acc (B ns) ⟨T, c⟩)| ≤
        ind (∃ k ∈ ks.toFinset, G.enc (r, k) ∈ T.usedIn) +
          iidAvg S ks.length (fun os => ∑ k ∈ ks.toFinset,
            Strat.touchIn (B (os.map G.out)) ⟨T, c⟩ (G.enc (r, k))) +
          (iidAvg S ks.length (fun os => Strat.touchAny (B (os.map G.out)) ⟨T, c⟩ os) +
            2 * ((ks.length : ℝ) * (T.length + ks.length) / Fintype.card S)) := by
    intro r
    have hrest1 := iidAvg_nonneg (n := ks.length) (hΨ0 r)
    have hrest2 := iidAvg_nonneg (n := ks.length) hΘ0
    by_cases hbad : ∃ k ∈ ks.toFinset, G.enc (r, k) ∈ T.usedIn
    · rw [ind_pos hbad]
      have h0 := Strat.exp_nonneg (fun os s' => Strat.acc_nonneg (B (os.map G.out)) s')
        (G.replies r ks) ⟨T, c⟩
      have h1 := Strat.exp_le zero_le_one (fun os s' => Strat.acc_le_one (B (os.map G.out)) s')
        (G.replies r ks) ⟨T, c⟩
      rw [abs_le]
      constructor <;> linarith
    · rw [ind_neg hbad, zero_add]
      have hfresh : ∀ k ∈ ks, G.enc (r, k) ∉ T.usedIn := fun k hk hmem =>
        hbad ⟨k, List.mem_toFinset.2 hk, hmem⟩
      have hZ0 : ∀ os, 0 ≤ (B (os.map G.out)).exp ⟨T, c⟩
          (fun _ s'' => ind (Strat.TouchedAny (G.ghosts r ks os) s''.trace)) :=
        fun os => Strat.exp_nonneg (fun _ _ => ind_nonneg _) _ _
      have hZ1 : ∀ os, (B (os.map G.out)).exp ⟨T, c⟩
          (fun _ s'' => ind (Strat.TouchedAny (G.ghosts r ks os) s''.trace)) ≤ 1 :=
        fun os => Strat.exp_le zero_le_one (fun _ _ => ind_le_one _) _ _
      -- the generator entries are ghosts for the second stage
      have step1 : |(G.replies r ks).exp ⟨T, c⟩
            (fun os s' => Strat.acc (B (os.map G.out)) s') -
          (G.replies r ks).exp ⟨T, c⟩ (fun os _ => Strat.acc (B (os.map G.out)) ⟨T, c⟩)| ≤
          (G.replies r ks).exp ⟨T, c⟩ (fun os _ => (B (os.map G.out)).exp ⟨T, c⟩
            (fun _ s'' => ind (Strat.TouchedAny (G.ghosts r ks os) s''.trace))) :=
        Strat.abs_exp_sub_le_exp (G.post_replies r ks T c hks hT hfresh)
          fun os s' hp => Strat.abs_exp_ghosts_le (G.ghosts r ks os) (fun b => ind (b = true))
            (fun _ => ind_nonneg _) (fun _ => ind_le_one _) (B (os.map G.out)) T s'.trace c
            s'.count hp.1 hp.2
      -- the replies against independent uniform states
      have step2 : |(G.replies r ks).exp ⟨T, c⟩
            (fun os _ => Strat.acc (B (os.map G.out)) ⟨T, c⟩) -
          iidAvg N ks.length (fun ns => Strat.acc (B ns) ⟨T, c⟩)| ≤
          (ks.length : ℝ) * (T.length + ks.length) / Fintype.card S := by
        rw [hideal]
        exact G.abs_exp_replies_sub_le r ks T c hks hT hfresh _ (fun _ => Strat.acc_nonneg _ _)
          (fun _ => Strat.acc_le_one _ _)
      have step3 := G.abs_exp_replies_sub_le r ks T c hks hT hfresh _ hZ0 hZ1
      have step4 : iidAvg S ks.length (fun os => (B (os.map G.out)).exp ⟨T, c⟩
            (fun _ s'' => ind (Strat.TouchedAny (G.ghosts r ks os) s''.trace))) ≤
          iidAvg S ks.length (fun os => ∑ k ∈ ks.toFinset,
            Strat.touchIn (B (os.map G.out)) ⟨T, c⟩ (G.enc (r, k))) +
          iidAvg S ks.length (fun os => Strat.touchAny (B (os.map G.out)) ⟨T, c⟩ os) := by
        rw [← iidAvg_add]
        exact iidAvg_mono fun os => G.touch_ghosts_le r ks T c os _ hfresh
      have t1 := abs_sub_le ((G.replies r ks).exp ⟨T, c⟩
          (fun os s' => Strat.acc (B (os.map G.out)) s'))
        ((G.replies r ks).exp ⟨T, c⟩ (fun os _ => Strat.acc (B (os.map G.out)) ⟨T, c⟩))
        (iidAvg N ks.length (fun ns => Strat.acc (B ns) ⟨T, c⟩))
      have t3 := (abs_le.1 step3).2
      linarith
  have hsum := (abs_avg_sub_le (univ : Finset R)
    (fun r => (G.replies r ks).exp ⟨T, c⟩ (fun os s' => Strat.acc (B (os.map G.out)) s'))
    (fun _ => iidAvg N ks.length (fun ns => Strat.acc (B ns) ⟨T, c⟩))).trans
    (avg_mono fun r _ => per_seed r)
  have hc1 : avg univ (fun _ : R => iidAvg N ks.length (fun ns => Strat.acc (B ns) ⟨T, c⟩)) =
      iidAvg N ks.length (fun ns => Strat.acc (B ns) ⟨T, c⟩) := avg_const univ_nonempty _
  have hc2 : avg univ (fun _ : R =>
      iidAvg S ks.length (fun os => Strat.touchAny (B (os.map G.out)) ⟨T, c⟩ os) +
        2 * ((ks.length : ℝ) * (T.length + ks.length) / Fintype.card S)) =
      iidAvg S ks.length (fun os => Strat.touchAny (B (os.map G.out)) ⟨T, c⟩ os) +
        2 * ((ks.length : ℝ) * (T.length + ks.length) / Fintype.card S) := avg_const univ_nonempty _
  have ha1 : avg univ (fun r : R => ind (∃ k ∈ ks.toFinset, G.enc (r, k) ∈ T.usedIn) +
        iidAvg S ks.length (fun os => ∑ k ∈ ks.toFinset,
          Strat.touchIn (B (os.map G.out)) ⟨T, c⟩ (G.enc (r, k))) +
        (iidAvg S ks.length (fun os => Strat.touchAny (B (os.map G.out)) ⟨T, c⟩ os) +
          2 * ((ks.length : ℝ) * (T.length + ks.length) / Fintype.card S))) =
      avg univ (fun r : R => ind (∃ k ∈ ks.toFinset, G.enc (r, k) ∈ T.usedIn) +
        iidAvg S ks.length (fun os => ∑ k ∈ ks.toFinset,
          Strat.touchIn (B (os.map G.out)) ⟨T, c⟩ (G.enc (r, k)))) +
      avg univ (fun _ : R =>
        iidAvg S ks.length (fun os => Strat.touchAny (B (os.map G.out)) ⟨T, c⟩ os) +
          2 * ((ks.length : ℝ) * (T.length + ks.length) / Fintype.card S)) := avg_add
  have ha2 : avg univ (fun r : R => ind (∃ k ∈ ks.toFinset, G.enc (r, k) ∈ T.usedIn) +
        iidAvg S ks.length (fun os => ∑ k ∈ ks.toFinset,
          Strat.touchIn (B (os.map G.out)) ⟨T, c⟩ (G.enc (r, k)))) =
      avg univ (fun r : R => ind (∃ k ∈ ks.toFinset, G.enc (r, k) ∈ T.usedIn)) +
      avg univ (fun r : R => iidAvg S ks.length (fun os => ∑ k ∈ ks.toFinset,
          Strat.touchIn (B (os.map G.out)) ⟨T, c⟩ (G.enc (r, k)))) := avg_add
  rw [hc1, ha1, ha2, hc2] at hsum
  have e1 := Strat.avg_bad_le (R := R) G.enc G.enc_inj ks.toFinset T hT
  have e2 : avg univ (fun r : R => iidAvg S ks.length (fun os => ∑ k ∈ ks.toFinset,
      Strat.touchIn (B (os.map G.out)) ⟨T, c⟩ (G.enc (r, k)))) ≤ (q2 : ℝ) / Fintype.card R := by
    rw [iidAvg_avg]
    exact iidAvg_le (by positivity) fun os =>
      Strat.avg_sum_touchIn_le G.enc G.enc_inj ks.toFinset (hB _) ⟨T, c⟩ hT
  have e3 := Strat.iidAvg_touchAny_le G.out F hF T c hT (T.length + q2) ks.length B
    (fun ns => Strat.post_usedOut_card (hB ns) ⟨T, c⟩ hT)
  push_cast at e3
  rw [add_div]
  linarith

theorem gen_core [Fintype R] [Nonempty R] [Fintype N] [Nonempty N] [DecidableEq N] [DecidableEq K]
    (F : ℕ) (hF : ∀ n : N, (univ.filter fun s => G.out s = n).card = F)
    (ks : List K) (hks : ks.Nodup) (B : List N → Strat S Bool) (q2 : ℕ)
    (hB : ∀ ns, (B ns).QB q2) (T : Trace S) (c : ℕ) (hT : T.WF) :
    |avg univ (fun r : R => (G.replies r ks).exp ⟨T, c⟩
          fun os s' => Strat.acc (B (os.map G.out)) s') -
        iidAvg N ks.length (fun ns => Strat.acc (B ns) ⟨T, c⟩)| ≤
      ((T.length : ℝ) + q2) / Fintype.card R + (ks.length : ℝ) * (T.length + q2) / F +
        2 * ((ks.length : ℝ) * (T.length + ks.length) / Fintype.card S) := by
  rcases ks with _ | ⟨k0, ks'⟩
  · have h0 : ∀ r : R, (G.replies r []).exp ⟨T, c⟩
        (fun os s' => Strat.acc (B (os.map G.out)) s') = Strat.acc (B []) ⟨T, c⟩ := fun _ => rfl
    rw [avg_congr fun r _ => h0 r, avg_const univ_nonempty]
    show |Strat.acc (B []) ⟨T, c⟩ - Strat.acc (B []) ⟨T, c⟩| ≤ _
    rw [sub_self, abs_zero]
    positivity
  · haveI : Nonempty S := ⟨G.enc (Classical.arbitrary R, k0)⟩
    exact G.gen_core_ne F hF _ hks B q2 hB T c hT

/-- **Generator indistinguishability.** `F` = states per revealed part (`out` is regular). With
`Q = q1 + ks.length + q2`: -/
theorem gen_bound [Fintype R] [Nonempty R] [Fintype N] [Nonempty N] [DecidableEq N] [DecidableEq K]
    (F : ℕ) (hF : ∀ n : N, (univ.filter fun s => G.out s = n).card = F)
    {σ : Type} (ks : List K) (hks : ks.Nodup) (A1 : Strat S σ) (A2 : σ → List N → Strat S Bool)
    (q1 q2 : ℕ) (hA1 : A1.QB q1) (hA2 : ∀ a ns, (A2 a ns).QB q2) :
    |(G.genReal ks A1 A2).prob PState.init (fun b _ => b = true) -
        (G.genIdeal ks.length A1 A2).prob PState.init (fun b _ => b = true)| ≤
      2 * ((q1 + ks.length + q2 : ℕ) : ℝ) / Fintype.card R +
        4 * ((q1 + ks.length + q2 : ℕ) : ℝ) * ks.length / F := by
  have hR : (G.genReal ks A1 A2).prob PState.init (fun b _ => b = true) =
      A1.exp PState.init (fun a s1 => avg univ fun r : R =>
        (G.replies r ks).exp s1 fun os s' => Strat.acc (A2 a (os.map G.out)) s') := by
    unfold genReal Strat.prob
    rw [Strat.exp_bind]
    congr 1
    funext a s1
    rw [Strat.exp_uniform]
    refine avg_congr fun r _ => ?_
    rw [Strat.exp_bind, G.exp_blocks]
    rfl
  have hI : (G.genIdeal ks.length A1 A2).prob PState.init (fun b _ => b = true) =
      A1.exp PState.init (fun a s1 => iidAvg N ks.length fun ns => Strat.acc (A2 a ns) s1) := by
    unfold genIdeal Strat.prob
    rw [Strat.exp_bind]
    congr 1
    funext a s1
    rw [Strat.exp_uniform, iidAvg_ofFn]
    rfl
  rw [hR, hI]
  refine Strat.abs_exp_sub_le_of_post Trace.WF.nil (Strat.post_run hA1 PState.init Trace.WF.nil) ?_
  rintro a ⟨T, c⟩ ⟨hT, -, hlen⟩
  have hlen' : (T.length : ℝ) ≤ q1 := by
    have h : T.length ≤ q1 := by simpa [PState.init] using hlen
    exact_mod_cast h
  refine (G.gen_core F hF ks hks (A2 a) q2 (hA2 a) T c hT).trans ?_
  have hSF : (Fintype.card S : ℝ) = F * Fintype.card N := card_eq_of_regular G.out F hF
  have hQ : ((q1 + ks.length + q2 : ℕ) : ℝ) = (q1 : ℝ) + ks.length + q2 := by push_cast; ring
  rw [hQ]
  have hL0 : (0 : ℝ) ≤ ks.length := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ T.length := Nat.cast_nonneg _
  have hq1 : (0 : ℝ) ≤ q1 := Nat.cast_nonneg _
  have hq2 : (0 : ℝ) ≤ q2 := Nat.cast_nonneg _
  have hR0 : (0 : ℝ) ≤ Fintype.card R := Nat.cast_nonneg _
  have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg _
  have t1 : ((T.length : ℝ) + q2) / Fintype.card R ≤
      2 * ((q1 : ℝ) + ks.length + q2) / Fintype.card R :=
    div_le_div_of_nonneg_right (by linarith) hR0
  have t2 : (ks.length : ℝ) * (T.length + q2) / F ≤
      ((q1 : ℝ) + ks.length + q2) * ks.length / F :=
    div_le_div_of_nonneg_right (by nlinarith) hF0
  have t3 : (ks.length : ℝ) * (T.length + ks.length) / Fintype.card S ≤
      ((q1 : ℝ) + ks.length + q2) * ks.length / F := by
    have hnum : (ks.length : ℝ) * (T.length + ks.length) ≤
        ((q1 : ℝ) + ks.length + q2) * ks.length := by nlinarith
    rcases hF0.eq_or_lt with hF | hF
    · rw [← hF, zero_mul] at hSF
      rw [hSF, ← hF, div_zero, div_zero]
    · have hN1 : (1 : ℝ) ≤ Fintype.card N := by exact_mod_cast Fintype.card_pos
      have hle : (F : ℝ) ≤ Fintype.card S := by rw [hSF]; nlinarith
      calc _ ≤ ((q1 : ℝ) + ks.length + q2) * ks.length / Fintype.card S :=
            div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _)
        _ ≤ ((q1 : ℝ) + ks.length + q2) * ks.length / F :=
            div_le_div_of_nonneg_left (by positivity) hF hle
  have t4 : 0 ≤ ((q1 : ℝ) + ks.length + q2) * ks.length / F := by positivity
  have e4 : 4 * ((q1 : ℝ) + ks.length + q2) * ks.length / F =
      4 * (((q1 : ℝ) + ks.length + q2) * ks.length / F) := by ring
  rw [e4]
  linarith

end GenCall

end CommitGolfCandidate.Permutation
