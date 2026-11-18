import CommitGolfCandidate.S4PermGen

/-!
# A whole layer of salted leaves in the lazy permutation model

Each leaf is hashed with two forward calls whose salt enters the FIRST call:
`o1 = π (enc1 (r, x))`, `o2 = π (enc2 (chop o1, m))`, digest `trunc o2`. A first stage `A1` (forward
and inverse access, private coins) chooses a list of leaves with pairwise different `x` and marks
each leaf hidden or opened. Real layer: every leaf draws a uniform salt and is hashed. Ideal layer:
a hidden leaf gets a uniform digest and makes no query. The second stage `A2` sees every digest
and the salts of the opened leaves only.

`SaltFirst.layer_bound`: the two experiments differ by at most
`2 (q1 + q2) / |R| + 8 n (q1 + Q2 + 2 n) (Kc + |D|) / |S|`, where `q2` counts only the forward
queries of `A2` on inputs of the shape of a first-call input.

Proof.

1. Coupling (`couple`). Run the ideal layer, and after the run draw "ghost data" for each hidden
   leaf: its salt, its first reply (uniform state) and its second reply (uniform in the fiber of
   its digest). The ghosts are the two table entries the real leaf would have made. The real
   experiment, run from the ghost table, is at least the ideal one weighted by "the ghosts are
   consistent and the ideal run never touched them" (several-ghost argument of `S4PermGen`).
2. The bad event. For fixed salts, the replies are uniform: a new reply hits the at most
   `M + 3 n` used values with probability `O ((M + n) (Kc + |D|) / |S|)` per leaf (`ghost_bad_le`).
   What remains is a hidden first-call input that the ideal run used; averaged over the salts this
   is `#(used ∩ hidden first-call inputs) / |R|`.
3. The used hidden first-call inputs (`ideal_cnt_le`): at most `q1` from the first stage (together
   with the first-call inputs of the opened leaves, which the opened leaves pay for with their own
   salts), at most `q2` shaped forward queries of `A2`, and inputs of second calls of opened leaves
   or inverse answers, which are fresh uniform values.

Mathlib only, on the definitions of `S3PermModel`.
-/

set_option linter.unusedSectionVars false

namespace CommitGolfCandidate.Permutation

open Finset

/-! ### Forward queries on shaped inputs -/

namespace Strat

variable {S : Type} {α β : Type}

/-- At most `n` forward queries on inputs satisfying `shape`, on every path (inverse queries and
forward queries on other inputs are not counted). -/
def FQB (shape : S → Prop) : Strat S α → ℕ → Prop
  | .done _, _ => True
  | .fwd x k, n =>
      (shape x → n ≠ 0 ∧ ∀ y, (k y).FQB shape (n - 1)) ∧ (¬ shape x → ∀ y, (k y).FQB shape n)
  | .inv _ k, n => ∀ x, (k x).FQB shape n
  | .rand _ k, n => ∀ i, (k i).FQB shape n

theorem FQB.mono {shape : S → Prop} {st : Strat S α} {n m : ℕ} (h : st.FQB shape n)
    (hnm : n ≤ m) : st.FQB shape m := by
  induction st generalizing n m with
  | done a => trivial
  | fwd x k ih =>
    refine ⟨fun hx => ⟨by have := (h.1 hx).1; omega, fun y => ih y ((h.1 hx).2 y) (by omega)⟩,
      fun hx y => ih y (h.2 hx y) hnm⟩
  | inv y k ih => exact fun x => ih x (h x) hnm
  | rand j k ih => exact fun i => ih i (h i) hnm

theorem FQB.bind {shape : S → Prop} {st : Strat S α} {f : α → Strat S β} {n m : ℕ}
    (h : st.FQB shape n) (hf : ∀ a, (f a).FQB shape m) : (st.bind f).FQB shape (n + m) := by
  induction st generalizing n with
  | done a => exact (hf a).mono (by omega)
  | fwd x k ih =>
    refine ⟨fun hx => ⟨by have := (h.1 hx).1; omega, fun y => ?_⟩, fun hx y => ih y (h.2 hx y)⟩
    have e : n + m - 1 = (n - 1) + m := by have := (h.1 hx).1; omega
    rw [e]
    exact ih y ((h.1 hx).2 y)
  | inv y k ih => exact fun x => ih x (h x)
  | rand j k ih => exact fun i => ih i (h i)

/-- Every query bound is a bound on the shaped forward queries. -/
theorem FQB_of_QB {shape : S → Prop} {st : Strat S α} {n : ℕ} (h : st.QB n) :
    st.FQB shape n := by
  induction h with
  | done a n => trivial
  | fwd x k n _ ih => exact ⟨fun _ => ⟨by omega, fun y => (ih y).mono (by omega)⟩,
      fun _ y => (ih y).mono (by omega)⟩
  | inv y k n _ ih => exact fun x => (ih x).mono (by omega)
  | rand j k n _ ih => exact fun i => ih i

theorem FQB_uniform {shape : S → Prop} {ι : Type} [Fintype ι] [Nonempty ι] {k : ι → Strat S α}
    {n : ℕ} (h : ∀ i, (k i).FQB shape n) : (uniform ι k).FQB shape n := fun _ => h _

/-- A forward query on an input without the shape is free. -/
theorem FQB_fwd_of_not {shape : S → Prop} {x : S} {k : S → Strat S α} {n : ℕ} (hx : ¬ shape x)
    (h : ∀ y, (k y).FQB shape n) : (Strat.fwd x k).FQB shape n :=
  ⟨fun h' => absurd h' hx, fun _ => h⟩

theorem bind_assoc (st : Strat S α) {γ : Type} (f : α → Strat S β) (g : β → Strat S γ) :
    (st.bind f).bind g = st.bind fun a => (f a).bind g := by
  induction st with
  | done a => rfl
  | fwd x k ih => simp only [Strat.bind, ih]
  | inv y k ih => simp only [Strat.bind, ih]
  | rand j k ih => simp only [Strat.bind, ih]

end Strat

/-! ### Averages -/

section avgs
variable {S : Type} [Fintype S] [DecidableEq S] {α : Type}

theorem Strat.exp_avg {ι : Type} (A : Finset ι) (F : ι → α → PState S → ℝ) (st : Strat S α)
    (s : PState S) :
    st.exp s (fun a s' => avg A fun i => F i a s') = avg A fun i => st.exp s (F i) := by
  unfold avg
  simp only [div_eq_inv_mul]
  rw [Strat.exp_mul_left, Strat.exp_sum]

theorem Strat.exp_eq_zero_of_touched (Γ : List (Entry S)) (st : Strat S α) (s : PState S)
    (V : α → PState S → ℝ) (hV : ∀ a s', Strat.TouchedAny Γ s'.trace → V a s' = 0)
    (h : Strat.TouchedAny Γ s.trace) : st.exp s V = 0 := by
  rw [Strat.exp_congr_of_post (Strat.post_suffix st s) (g := fun _ _ => 0), Strat.exp_zero]
  intro a s' hs
  exact hV a s' (h.mono hs)

/-- Averaging over the fibers of a regular map and then over the image is averaging over the
whole space. -/
theorem avg_fiber {D : Type} [Fintype D] [DecidableEq D] (tr : S → D) (F : ℕ)
    (hF : ∀ d, (univ.filter fun s => tr s = d).card = F) (g : D → S → ℝ) :
    avg univ (fun d => avg (univ.filter fun o => tr o = d) (g d)) =
      avg univ (fun o => g (tr o) o) := by
  have hS := card_eq_of_regular tr F hF
  unfold avg
  simp only [hF, Finset.card_univ]
  rw [hS, ← Finset.sum_div, div_div, ← Finset.sum_fiberwise univ tr (fun o => g (tr o) o)]
  congr 1
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun o ho => ?_
  rw [(Finset.mem_filter.1 ho).2]

theorem avg_ind_mem_le {ι : Type} (A B : Finset ι) (p : ι → Prop) (h : ∀ i ∈ A, p i → i ∈ B) :
    avg A (fun i => ind (p i)) ≤ (B.card : ℝ) / A.card := by
  unfold avg
  exact div_le_div_of_nonneg_right (sum_ind_le A B p h) (Nat.cast_nonneg _)

theorem avg_le_of_le_ind_add {ι : Type} (A : Finset ι) (g : ι → ℝ) (p : ι → Prop) (c : ℝ)
    (hc : 0 ≤ c) (h : ∀ i ∈ A, g i ≤ ind (p i) + c) :
    avg A g ≤ avg A (fun i => ind (p i)) + c := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp [avg, hc]
  · refine (avg_mono h).trans ?_
    rw [avg_add, avg_const hA]

end avgs

/-! ### The salted two-call hash and the layer -/

variable {S : Type} [Fintype S] [DecidableEq S] {R X C M2 D : Type}

/-- A two-call hash whose salt enters the FIRST call. `X` carries the tag and the first message part. -/
structure SaltFirst (S R X C M2 D : Type) where
  enc1 : R × X → S
  enc1_inj : Function.Injective enc1
  chop : S → C
  enc2 : C × M2 → S
  enc2_inj : Function.Injective enc2
  trunc : S → D

/-- One leaf of the layer. `hidden = false`: the second stage will also see the salt. -/
structure LeafSpec (X M2 : Type) where
  x : X
  m : M2
  hidden : Bool

namespace SaltFirst
variable (H : SaltFirst S R X C M2 D)

def eval (r : R) (l : LeafSpec X M2) : Strat S D :=
  .fwd (H.enc1 (r, l.x)) fun o1 => .fwd (H.enc2 (H.chop o1, l.m)) fun o2 => .done (H.trunc o2)

/-- Real layer: every leaf draws a salt and is hashed. Output per leaf: digest and salt. -/
noncomputable def layerReal [Fintype R] [Nonempty R] : List (LeafSpec X M2) → Strat S (List (D × R))
  | [] => .done []
  | l :: ls => Strat.uniform R fun r => (H.eval r l).bind fun d =>
      (layerReal ls).bind fun out => .done ((d, r) :: out)

/-- Ideal layer: a hidden leaf gets a uniform digest and makes no query. -/
noncomputable def layerIdeal [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] :
    List (LeafSpec X M2) → Strat S (List (D × R))
  | [] => .done []
  | l :: ls => Strat.uniform R fun r =>
      (if l.hidden then Strat.uniform D fun d => Strat.done d else H.eval r l).bind fun d =>
        (layerIdeal ls).bind fun out => .done ((d, r) :: out)

/-- What the second stage sees: every digest, and the salt of the opened leaves only. -/
def view (ls : List (LeafSpec X M2)) (out : List (D × R)) : List (D × Option R) :=
  List.zipWith (fun l p => (p.1, if l.hidden then none else some p.2)) ls out

/-! ### Ghosts, the bad event and the counts -/

/-- The first-call table entry of a hidden leaf. -/
def ghost1 (r : R) (x : X) (o1 : S) : Entry S := ⟨.fwd, H.enc1 (r, x), o1⟩

/-- The second-call table entry of a hidden leaf. -/
def ghost2 (o1 : S) (m : M2) (o2 : S) : Entry S := ⟨.fwd, H.enc2 (H.chop o1, m), o2⟩

/-- The ghosts are not a partial bijection, or the table `t` touches one of them. -/
def GhostBad (Γ : List (Entry S)) (t : Trace S) : Prop :=
  ¬ (Γ.map Entry.inp).Nodup ∨ ¬ (Γ.map Entry.out).Nodup ∨ Strat.TouchedAny Γ t

/-- Average over the ghost data of the hidden leaves: per hidden leaf a uniform salt, a uniform
first reply and a second reply uniform in the fiber of the leaf's digest. -/
noncomputable def ghostAvg [Fintype R] [DecidableEq D] :
    List (LeafSpec X M2) → List (D × R) → (List (Entry S) → ℝ) → ℝ
  | [], _, φ => φ []
  | _ :: _, [], φ => φ []
  | l :: ls, p :: out, φ =>
      if l.hidden then
        avg univ fun r : R => avg univ fun o1 : S =>
          avg (univ.filter fun o2 => H.trunc o2 = p.1) fun o2 =>
            ghostAvg ls out fun Γ => φ (H.ghost1 r l.x o1 :: H.ghost2 o1 l.m o2 :: Γ)
      else ghostAvg ls out φ

/-- Number of hidden leaves. -/
def hcount (ls : List (LeafSpec X M2)) : ℕ := (ls.filter fun l => l.hidden).length

/-- The `x` of the hidden leaves. -/
def hidX [DecidableEq X] (ls : List (LeafSpec X M2)) : Finset X :=
  ((ls.filter fun l => l.hidden).map LeafSpec.x).toFinset

/-- The `x` of the opened leaves. -/
def openX [DecidableEq X] (ls : List (LeafSpec X M2)) : Finset X :=
  ((ls.filter fun l => !l.hidden).map LeafSpec.x).toFinset

/-- Number of pairs (salt, `x ∈ P`) whose first-call input is in `U`. -/
def cnt [Fintype R] [DecidableEq X] (P : Finset X) (U : Finset S) : ℕ :=
  ((univ ×ˢ P).filter fun p => H.enc1 p ∈ U).card

/-! ### The steps of the proof -/

/-! ### The coupling -/

theorem ghostAvg_zero [Fintype R] [DecidableEq D] :
    ∀ (ls : List (LeafSpec X M2)) (out : List (D × R)) (φ : List (Entry S) → ℝ),
      (∀ Γ, φ Γ = 0) → H.ghostAvg ls out φ = 0
  | [], _, φ, h => h []
  | _ :: _, [], φ, h => h []
  | l :: ls, p :: out, φ, h => by
    simp only [ghostAvg]
    split_ifs
    · simp only [ghostAvg_zero ls out _ fun Γ => h _, avg_zero]
    · exact ghostAvg_zero ls out φ h

/-- The value of the ideal layer, weighted by "the ghosts are consistent and untouched". -/
noncomputable def idealVal [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [DecidableEq D]
    (f : Bool → ℝ) (ls : List (LeafSpec X M2)) (B : List (D × Option R) → Strat S Bool)
    (Γ0 : List (Entry S)) (s : PState S) : ℝ :=
  (H.layerIdeal ls).exp s (fun out s1 => (B (view ls out)).exp s1 fun b s' =>
    H.ghostAvg ls out fun Γ => ind (¬ GhostBad (Γ0 ++ Γ) s'.trace) * f b)

/-- The value of the real layer. -/
noncomputable def realVal [Fintype R] [Nonempty R] (f : Bool → ℝ) (ls : List (LeafSpec X M2))
    (B : List (D × Option R) → Strat S Bool) (s : PState S) : ℝ :=
  (H.layerReal ls).exp s (fun out s1 => (B (view ls out)).exp s1 fun b _ => f b)

theorem realVal_nonneg [Fintype R] [Nonempty R] (f : Bool → ℝ) (hf0 : ∀ b, 0 ≤ f b)
    (ls : List (LeafSpec X M2)) (B : List (D × Option R) → Strat S Bool) (s : PState S) :
    0 ≤ H.realVal f ls B s :=
  Strat.exp_nonneg (fun _ _ => Strat.exp_nonneg (fun _ _ => hf0 _) _ _) _ _

theorem realVal_cons [Fintype R] [Nonempty R] (f : Bool → ℝ) (l : LeafSpec X M2)
    (ls : List (LeafSpec X M2)) (B : List (D × Option R) → Strat S Bool) (s : PState S) :
    H.realVal f (l :: ls) B s = avg univ fun r => (H.eval r l).exp s fun d s1 =>
      H.realVal f ls (fun v => B ((d, if l.hidden then none else some r) :: v)) s1 := by
  unfold realVal
  simp only [layerReal]
  rw [Strat.exp_uniform]
  refine avg_congr fun r _ => ?_
  rw [Strat.exp_bind]
  congr 1
  funext d s1
  rw [Strat.exp_bind]
  rfl

theorem idealVal_zero [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [DecidableEq D]
    (f : Bool → ℝ) (ls : List (LeafSpec X M2)) (B : List (D × Option R) → Strat S Bool)
    (Γ0 : List (Entry S)) (s : PState S)
    (h : ∀ Γ (t : Trace S), s.trace <:+ t → GhostBad (Γ0 ++ Γ) t) :
    H.idealVal f ls B Γ0 s = 0 := by
  unfold idealVal
  rw [Strat.exp_congr_of_post (Strat.post_suffix _ s) (g := fun _ _ => 0), Strat.exp_zero]
  intro out s1 hs1
  rw [Strat.exp_congr_of_post (Strat.post_suffix _ s1) (g := fun _ _ => 0), Strat.exp_zero]
  intro b s' hs'
  exact H.ghostAvg_zero ls out _ fun Γ => by
    rw [ind_neg (not_not.2 (h Γ s'.trace (hs1.trans hs'))), zero_mul]

theorem idealVal_cons_open [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [DecidableEq D]
    (f : Bool → ℝ) (l : LeafSpec X M2) (hl : l.hidden = false) (ls : List (LeafSpec X M2))
    (B : List (D × Option R) → Strat S Bool) (Γ0 : List (Entry S)) (s : PState S) :
    H.idealVal f (l :: ls) B Γ0 s = avg univ fun r => (H.eval r l).exp s fun d s1 =>
      H.idealVal f ls (fun v => B ((d, some r) :: v)) Γ0 s1 := by
  unfold idealVal
  simp only [layerIdeal, hl]
  rw [Strat.exp_uniform]
  refine avg_congr fun r _ => ?_
  simp only [Bool.false_eq_true, if_false]
  rw [Strat.exp_bind]
  congr 1
  funext d s1
  rw [Strat.exp_bind]
  simp only [Strat.exp, view, List.zipWith_cons_cons, ghostAvg, hl, Bool.false_eq_true, if_false]

theorem idealVal_cons_hidden [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [DecidableEq D]
    (F : ℕ) (hF : ∀ d : D, (Finset.univ.filter fun s => H.trunc s = d).card = F)
    (f : Bool → ℝ) (l : LeafSpec X M2) (hl : l.hidden = true) (ls : List (LeafSpec X M2))
    (B : List (D × Option R) → Strat S Bool) (Γ0 : List (Entry S)) (s : PState S) :
    H.idealVal f (l :: ls) B Γ0 s = avg univ fun r : R => avg univ fun o1 : S => avg univ fun o2 : S =>
      H.idealVal f ls (fun v => B ((H.trunc o2, none) :: v))
        (Γ0 ++ [H.ghost1 r l.x o1, H.ghost2 o1 l.m o2]) s := by
  have step : ∀ (d : D) (r0 : R), (H.layerIdeal ls).exp s (fun out s1 =>
      (B (view (l :: ls) ((d, r0) :: out))).exp s1 fun b s' =>
        H.ghostAvg (l :: ls) ((d, r0) :: out) fun Γ => ind (¬ GhostBad (Γ0 ++ Γ) s'.trace) * f b) =
      avg univ fun r : R => avg univ fun o1 : S => avg (univ.filter fun o2 => H.trunc o2 = d) fun o2 =>
        H.idealVal f ls (fun v => B ((d, none) :: v))
          (Γ0 ++ [H.ghost1 r l.x o1, H.ghost2 o1 l.m o2]) s := by
    intro d r0
    unfold idealVal
    simp only [view, List.zipWith_cons_cons, ghostAvg, hl, if_true, Strat.exp_avg,
      List.append_assoc, List.cons_append, List.nil_append]
  have hS : ∀ r' : R, ((Strat.uniform D fun d => Strat.done d).bind fun d =>
      (H.layerIdeal ls).bind fun out => Strat.done ((d, r') :: out)).exp s
        (fun out s1 => (B (view (l :: ls) out)).exp s1 fun b s' =>
          H.ghostAvg (l :: ls) out fun Γ => ind (¬ GhostBad (Γ0 ++ Γ) s'.trace) * f b) =
      avg univ fun d : D => avg univ fun r : R => avg univ fun o1 : S =>
        avg (univ.filter fun o2 => H.trunc o2 = d) fun o2 =>
          H.idealVal f ls (fun v => B ((d, none) :: v))
            (Γ0 ++ [H.ghost1 r l.x o1, H.ghost2 o1 l.m o2]) s := by
    intro r'
    rw [Strat.exp_bind, Strat.exp_uniform]
    refine avg_congr fun d _ => ?_
    show ((H.layerIdeal ls).bind fun out => Strat.done ((d, r') :: out)).exp s _ = _
    rw [Strat.exp_bind]
    exact step d r'
  unfold idealVal
  simp only [layerIdeal, hl, if_true]
  rw [Strat.exp_uniform]
  rw [avg_congr fun r' _ => hS r', avg_const univ_nonempty]
  rw [avg_comm]
  refine avg_congr fun r _ => ?_
  rw [avg_comm]
  refine avg_congr fun o1 _ => ?_
  rw [avg_fiber H.trunc F hF (fun d o2 => H.idealVal f ls (fun v => B ((d, none) :: v))
    (Γ0 ++ [H.ghost1 r l.x o1, H.ghost2 o1 l.m o2]) s)]
  rfl

theorem GhostBad.of_inp_dup {Γ0 L : List (Entry S)} {t : Trace S} {g g' : Entry S} (hg : g ∈ Γ0)
    (hg' : g' ∈ L) (h : g.inp = g'.inp) : GhostBad (Γ0 ++ L) t := by
  left
  intro hn
  rw [List.map_append, List.nodup_append] at hn
  exact hn.2.2 _ (List.mem_map_of_mem hg) _ (List.mem_map_of_mem hg') h

theorem GhostBad.of_out_dup {Γ0 L : List (Entry S)} {t : Trace S} {g g' : Entry S} (hg : g ∈ Γ0)
    (hg' : g' ∈ L) (h : g.out = g'.out) : GhostBad (Γ0 ++ L) t := by
  right; left
  intro hn
  rw [List.map_append, List.nodup_append] at hn
  exact hn.2.2 _ (List.mem_map_of_mem hg) _ (List.mem_map_of_mem hg') h

theorem GhostBad.of_touched {L : List (Entry S)} {t : Trace S} {g : Entry S} (hg : g ∈ L)
    (h : Strat.Touched g t) : GhostBad L t := Or.inr (Or.inr ⟨g, hg, h⟩)

theorem GhostBad.of_pair_inp {Γ0 Γ : List (Entry S)} {t : Trace S} {g1 g2 : Entry S}
    (h : g1.inp = g2.inp) : GhostBad (Γ0 ++ g1 :: g2 :: Γ) t := by
  left
  intro hn
  rw [List.map_append, List.nodup_append] at hn
  have h2 := hn.2.1
  simp only [List.map_cons, List.nodup_cons, List.mem_cons] at h2
  exact h2.1 (Or.inl h)

theorem GhostBad.of_pair_out {Γ0 Γ : List (Entry S)} {t : Trace S} {g1 g2 : Entry S}
    (h : g1.out = g2.out) : GhostBad (Γ0 ++ g1 :: g2 :: Γ) t := by
  right; left
  intro hn
  rw [List.map_append, List.nodup_append] at hn
  have h2 := hn.2.1
  simp only [List.map_cons, List.nodup_cons, List.mem_cons] at h2
  exact h2.1 (Or.inl h)

/-- One forward query, with ghosts `Γ0` in the second table. -/
theorem ghost_fwd_le {β : Type} (Γ0 : List (Entry S)) (x : S) (k1 k2 : S → Strat S β)
    (V1 V2 : β → PState S → ℝ) (hV1 : ∀ a s', Strat.TouchedAny Γ0 s'.trace → V1 a s' = 0)
    (hV2 : ∀ a s', 0 ≤ V2 a s')
    (IH : ∀ y (T1 t1 : Trace S) (c1 c1' : ℕ), t1.Perm (Γ0 ++ T1) → t1.WF →
      (k1 y).exp ⟨T1, c1⟩ V1 ≤ (k2 y).exp ⟨t1, c1'⟩ V2)
    (T t' : Trace S) (c c' : ℕ) (hp : t'.Perm (Γ0 ++ T)) (hwf' : t'.WF) :
    (Strat.fwd x k1).exp ⟨T, c⟩ V1 ≤ (Strat.fwd x k2).exp ⟨t', c'⟩ V2 := by
  simp only [Strat.exp]
  have hR0 : 0 ≤ avg (t'.fwdAns x) fun y => (k2 y).exp ⟨t'.stepF x y, c' + 1⟩ V2 :=
    avg_nonneg fun y _ => Strat.exp_nonneg hV2 _ _
  by_cases hxg : ∃ g ∈ Γ0, g.inp = x
  · have hz : ∀ y ∈ T.fwdAns x, (k1 y).exp ⟨T.stepF x y, c + 1⟩ V1 = 0 := fun y _ => by
      obtain ⟨g, hg, hgx⟩ := hxg
      exact Strat.exp_eq_zero_of_touched Γ0 _ _ V1 hV1
        ⟨g, hg, Or.inl (by rw [hgx]; exact Trace.mem_usedIn_stepF T x y)⟩
    rw [avg_congr hz, avg_zero]
    exact hR0
  · push_neg at hxg
    by_cases hx : x ∈ T.usedIn
    · have hx' : x ∈ t'.usedIn := (Trace.mem_usedIn_perm_append hp).2 (Or.inr hx)
      have e1 : T.fwdAns x = T.fwdHits x := if_pos hx
      have e2 : t'.fwdAns x = T.fwdHits x :=
        (if_pos hx').trans (Trace.fwdHits_perm_append hp hxg)
      have e3 : ∀ y, T.stepF x y = T := fun y => if_pos hx
      have e4 : ∀ y, t'.stepF x y = t' := fun y => if_pos hx'
      simp only [e1, e2, e3, e4]
      exact avg_mono fun y _ => IH y T t' _ _ hp hwf'
    · have hx' : x ∉ t'.usedIn := fun h =>
        ((Trace.mem_usedIn_perm_append hp).1 h).elim (fun ⟨g, hg, hgx⟩ => hxg g hg hgx) hx
      have e1 : T.fwdAns x = T.freeOut := if_neg hx
      have e2 : t'.fwdAns x = t'.freeOut := if_neg hx'
      have e3 : ∀ y, T.stepF x y = ⟨.fwd, x, y⟩ :: T := fun y => if_neg hx
      have e4 : ∀ y, t'.stepF x y = ⟨.fwd, x, y⟩ :: t' := fun y => if_neg hx'
      simp only [e1, e2, e3, e4]
      have hsub : t'.freeOut ⊆ T.freeOut := fun y hy => by
        rw [Trace.mem_freeOut] at hy ⊢
        exact fun h => hy ((Trace.mem_usedOut_perm_append hp).2 (Or.inr h))
      refine avg_le_avg_of_subset hsub ?_ ?_ ?_
      · intro y hy hny
        have hyu : y ∈ t'.usedOut := by
          by_contra h
          exact hny (Trace.mem_freeOut.2 h)
        rcases (Trace.mem_usedOut_perm_append hp).1 hyu with ⟨g, hg, hgy⟩ | h
        · exact (Strat.exp_eq_zero_of_touched Γ0 _ _ V1 hV1 ⟨g, hg, Or.inr
            (Trace.mem_usedOut.2 ⟨⟨.fwd, x, y⟩, List.mem_cons_self, hgy.symm⟩)⟩).le
        · exact absurd h (Trace.mem_freeOut.1 hy)
      · intro y hy
        exact IH y _ _ _ _ ((hp.cons _).trans List.perm_middle.symm)
          (hwf'.cons hx' (Trace.mem_freeOut.1 hy))
      · intro y _
        exact Strat.exp_nonneg hV2 _ _

theorem idealVal_zero_of_touched [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [DecidableEq D]
    (f : Bool → ℝ) (ls : List (LeafSpec X M2)) (B : List (D × Option R) → Strat S Bool)
    (Γ0 : List (Entry S)) (s : PState S) (h : Strat.TouchedAny Γ0 s.trace) :
    H.idealVal f ls B Γ0 s = 0 :=
  H.idealVal_zero f ls B Γ0 s fun Γ t hst => by
    obtain ⟨g, hg, hT⟩ := h.mono hst
    exact GhostBad.of_touched (List.mem_append_left _ hg) hT

/-- The hidden leaf: its two real queries against the ideal run's ghosts. -/
theorem hidden_step [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [DecidableEq D]
    (f : Bool → ℝ) (hf0 : ∀ b, 0 ≤ f b) (l : LeafSpec X M2) (ls : List (LeafSpec X M2))
    (ih : ∀ (B : List (D × Option R) → Strat S Bool) (Γ0 : List (Entry S)) (T t' : Trace S)
      (c c' : ℕ), t'.Perm (Γ0 ++ T) → t'.WF →
        H.idealVal f ls B Γ0 ⟨T, c⟩ ≤ H.realVal f ls B ⟨t', c'⟩)
    (B : List (D × Option R) → Strat S Bool) (Γ0 : List (Entry S)) (T t' : Trace S) (c c' : ℕ)
    (hp : t'.Perm (Γ0 ++ T)) (hwf : t'.WF) (r : R) :
    avg univ (fun o1 : S => avg univ fun o2 : S =>
        H.idealVal f ls (fun v => B ((H.trunc o2, none) :: v))
          (Γ0 ++ [H.ghost1 r l.x o1, H.ghost2 o1 l.m o2]) ⟨T, c⟩) ≤
      (H.eval r l).exp ⟨t', c'⟩ fun d s1 => H.realVal f ls (fun v => B ((d, none) :: v)) s1 := by
  -- the ideal value vanishes as soon as the ghosts are inconsistent with `Γ0`, `T` or each other
  have hz : ∀ o1 o2, (∀ Γ (t : Trace S), T <:+ t →
      GhostBad (Γ0 ++ H.ghost1 r l.x o1 :: H.ghost2 o1 l.m o2 :: Γ) t) →
      H.idealVal f ls (fun v => B ((H.trunc o2, none) :: v))
        (Γ0 ++ [H.ghost1 r l.x o1, H.ghost2 o1 l.m o2]) ⟨T, c⟩ = 0 := fun o1 o2 h =>
    H.idealVal_zero f ls _ _ _ fun Γ t ht => by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using h Γ t ht
  have hR0 : ∀ s1 : PState S, ∀ d, 0 ≤ H.realVal f ls (fun v => B ((d, none) :: v)) s1 :=
    fun s1 d => H.realVal_nonneg f hf0 ls _ s1
  have hm1 : ∀ g1 g2 : Entry S, ∀ Γ, g1 ∈ g1 :: g2 :: Γ := fun _ _ _ => List.mem_cons_self
  have hm2 : ∀ g1 g2 : Entry S, ∀ Γ, g2 ∈ g1 :: g2 :: Γ :=
    fun _ _ _ => List.mem_cons_of_mem _ List.mem_cons_self
  simp only [eval, Strat.exp]
  set x1 := H.enc1 (r, l.x) with hx1def
  by_cases hx1 : x1 ∈ t'.usedIn
  · have h0 : ∀ o1 o2, H.idealVal f ls (fun v => B ((H.trunc o2, none) :: v))
        (Γ0 ++ [H.ghost1 r l.x o1, H.ghost2 o1 l.m o2]) ⟨T, c⟩ = 0 := fun o1 o2 =>
      hz o1 o2 fun Γ t ht => by
        rcases (Trace.mem_usedIn_perm_append hp).1 hx1 with ⟨g, hg, hgx⟩ | hT1
        · exact GhostBad.of_inp_dup hg (hm1 _ _ Γ) hgx
        · exact GhostBad.of_touched (List.mem_append_right _ (hm1 _ _ Γ))
            (Or.inl (usedIn_subset_of_suffix ht hT1))
    rw [avg_congr fun o1 _ => avg_congr fun o2 _ => h0 o1 o2]
    simp only [avg_zero]
    exact avg_nonneg fun o1 _ => avg_nonneg fun o2 _ => hR0 _ _
  · have e1 : t'.fwdAns x1 = t'.freeOut := if_neg hx1
    have e3 : ∀ o1, t'.stepF x1 o1 = ⟨.fwd, x1, o1⟩ :: t' := fun o1 => if_neg hx1
    simp only [e1, e3]
    refine avg_le_avg_of_subset (Finset.subset_univ _) ?_ ?_ ?_
    · intro o1 _ ho1
      have ho1' : o1 ∈ t'.usedOut := by
        by_contra h
        exact ho1 (Trace.mem_freeOut.2 h)
      have h0 : ∀ o2, H.idealVal f ls (fun v => B ((H.trunc o2, none) :: v))
          (Γ0 ++ [H.ghost1 r l.x o1, H.ghost2 o1 l.m o2]) ⟨T, c⟩ = 0 := fun o2 =>
        hz o1 o2 fun Γ t ht => by
          rcases (Trace.mem_usedOut_perm_append hp).1 ho1' with ⟨g, hg, hgo⟩ | hT1
          · exact GhostBad.of_out_dup hg (hm1 _ _ Γ) hgo
          · exact GhostBad.of_touched (List.mem_append_right _ (hm1 _ _ Γ))
              (Or.inr (usedOut_subset_of_suffix ht hT1))
      rw [avg_congr fun o2 _ => h0 o2, avg_zero]
    · intro o1 ho1
      have hwf1 : Trace.WF (⟨.fwd, x1, o1⟩ :: t') := hwf.cons hx1 (Trace.mem_freeOut.1 ho1)
      set t1 : Trace S := ⟨.fwd, x1, o1⟩ :: t' with ht1
      set x2 := H.enc2 (H.chop o1, l.m) with hx2def
      by_cases hx2 : x2 ∈ t1.usedIn
      · have h0 : ∀ o2, H.idealVal f ls (fun v => B ((H.trunc o2, none) :: v))
            (Γ0 ++ [H.ghost1 r l.x o1, H.ghost2 o1 l.m o2]) ⟨T, c⟩ = 0 := fun o2 =>
          hz o1 o2 fun Γ t ht => by
            obtain ⟨e, he, hex⟩ := Trace.mem_usedIn.1 hx2
            rcases List.mem_cons.1 he with rfl | he'
            · exact GhostBad.of_pair_inp hex
            · have hx2' : x2 ∈ t'.usedIn := Trace.mem_usedIn.2 ⟨e, he', hex⟩
              rcases (Trace.mem_usedIn_perm_append hp).1 hx2' with ⟨g, hg, hgx⟩ | hT1
              · exact GhostBad.of_inp_dup hg (hm2 _ _ Γ) hgx
              · exact GhostBad.of_touched (List.mem_append_right _ (hm2 _ _ Γ))
                  (Or.inl (usedIn_subset_of_suffix ht hT1))
        rw [avg_congr fun o2 _ => h0 o2, avg_zero]
        exact avg_nonneg fun o2 _ => hR0 _ _
      · have e2 : t1.fwdAns x2 = t1.freeOut := if_neg hx2
        have e4 : ∀ o2, t1.stepF x2 o2 = ⟨.fwd, x2, o2⟩ :: t1 := fun o2 => if_neg hx2
        simp only [e2, e4]
        refine avg_le_avg_of_subset (Finset.subset_univ _) ?_ ?_ ?_
        · intro o2 _ ho2
          have ho2' : o2 ∈ t1.usedOut := by
            by_contra h
            exact ho2 (Trace.mem_freeOut.2 h)
          refine (hz o1 o2 fun Γ t ht => ?_).le
          obtain ⟨e, he, heo⟩ := Trace.mem_usedOut.1 ho2'
          rcases List.mem_cons.1 he with rfl | he'
          · exact GhostBad.of_pair_out heo
          · have ho2'' : o2 ∈ t'.usedOut := Trace.mem_usedOut.2 ⟨e, he', heo⟩
            rcases (Trace.mem_usedOut_perm_append hp).1 ho2'' with ⟨g, hg, hgo⟩ | hT1
            · exact GhostBad.of_out_dup hg (hm2 _ _ Γ) hgo
            · exact GhostBad.of_touched (List.mem_append_right _ (hm2 _ _ Γ))
                (Or.inr (usedOut_subset_of_suffix ht hT1))
        · intro o2 ho2
          have hwf2 : Trace.WF (⟨.fwd, x2, o2⟩ :: t1) := hwf1.cons hx2 (Trace.mem_freeOut.1 ho2)
          refine ih _ _ T _ c _ ?_ hwf2
          rw [List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
          exact ((hp.cons _).cons _).trans ((List.Perm.swap _ _ _).trans
            ((List.perm_middle.symm.cons _).trans List.perm_middle.symm))
        · intro o2 _
          exact hR0 _ _
    · intro o1 _
      exact avg_nonneg fun o2 _ => hR0 _ _

/-- Coupling: the ideal run weighted by "the ghosts are consistent and untouched" is at most
the real run from the table with the ghosts `Γ0` of the earlier hidden leaves. -/
theorem couple [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [DecidableEq D] (F : ℕ)
    (hF : ∀ d : D, (Finset.univ.filter fun s => H.trunc s = d).card = F)
    (f : Bool → ℝ) (hf0 : ∀ b, 0 ≤ f b) :
    ∀ (ls : List (LeafSpec X M2)) (B : List (D × Option R) → Strat S Bool) (Γ0 : List (Entry S))
      (T t' : Trace S) (c c' : ℕ), t'.Perm (Γ0 ++ T) → t'.WF →
      (H.layerIdeal ls).exp ⟨T, c⟩ (fun out s => (B (view ls out)).exp s fun b s' =>
          H.ghostAvg ls out fun Γ => ind (¬ GhostBad (Γ0 ++ Γ) s'.trace) * f b) ≤
        (H.layerReal ls).exp ⟨t', c'⟩ (fun out s => (B (view ls out)).exp s fun b _ => f b) := by
  intro ls
  induction ls with
  | nil =>
    intro B Γ0 T t' c c' hp hwf
    have hn1 : (Γ0.map Entry.inp).Nodup := by
      have := (hp.map Entry.inp).nodup_iff.1 hwf.inp
      rw [List.map_append] at this
      exact this.of_append_left
    have hn2 : (Γ0.map Entry.out).Nodup := by
      have := (hp.map Entry.out).nodup_iff.1 hwf.out
      rw [List.map_append] at this
      exact this.of_append_left
    have key : ∀ t : Trace S, ind (¬ GhostBad (Γ0 ++ []) t) = ind (¬ Strat.TouchedAny Γ0 t) := by
      intro t
      rw [List.append_nil]
      unfold GhostBad
      congr 1
      apply propext
      simp only [hn1, hn2, not_true_eq_false, false_or]
    simp only [layerIdeal, layerReal, Strat.exp, view, List.zipWith_nil_left, ghostAvg, key]
    exact Strat.exp_ghosts_le Γ0 f hf0 (B []) T t' c c' hp hwf
  | cons l ls ih =>
    intro B Γ0 T t' c c' hp hwf
    show H.idealVal f (l :: ls) B Γ0 ⟨T, c⟩ ≤ H.realVal f (l :: ls) B ⟨t', c'⟩
    rw [H.realVal_cons]
    cases hl : l.hidden
    · rw [H.idealVal_cons_open f l hl]
      simp only [Bool.false_eq_true, ite_false]
      refine avg_mono fun r _ => ?_
      have hV1 : ∀ (d : D) (s' : PState S), Strat.TouchedAny Γ0 s'.trace →
          H.idealVal f ls (fun v => B ((d, some r) :: v)) Γ0 s' = 0 :=
        fun d s' h => H.idealVal_zero_of_touched f ls _ Γ0 s' h
      have hV2 : ∀ (d : D) (s' : PState S),
          0 ≤ H.realVal f ls (fun v => B ((d, some r) :: v)) s' :=
        fun d s' => H.realVal_nonneg f hf0 ls _ s'
      refine ghost_fwd_le Γ0 _ _ _ _ _ hV1 hV2 ?_ T t' c c' hp hwf
      intro o1 T1 t1 c1 c1' hp1 hwf1
      refine ghost_fwd_le Γ0 _ _ _ _ _ hV1 hV2 ?_ T1 t1 c1 c1' hp1 hwf1
      intro o2 T2 t2 c2 c2' hp2 hwf2
      exact ih (fun v => B ((H.trunc o2, some r) :: v)) Γ0 T2 t2 c2 c2' hp2 hwf2
    · rw [H.idealVal_cons_hidden F hF f l hl]
      simp only [ite_true]
      exact avg_mono fun r _ => H.hidden_step f hf0 l ls (fun B Γ0 T t' c c' hp hwf =>
        ih B Γ0 T t' c c' hp hwf) B Γ0 T t' c c' hp hwf r

/-! ### Helpers for the bad event -/

theorem l2_avg_add_const_le {ι : Type} (A : Finset ι) (g : ι → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    avg A (fun i => g i + c) ≤ avg A g + c := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp [avg, hc]
  · rw [avg_add, avg_const hA]

theorem l2_avg_split {ι : Type} (A : Finset ι) (f g : ι → ℝ) (b c bf bg : ℝ) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hf : avg A f ≤ bf) (hg : avg A g ≤ bg) :
    avg A (fun i => b + (f i + g i + c)) ≤ bf + bg + (b + c) := by
  have e : (fun i => b + (f i + g i + c)) = fun i => (f i + g i) + (b + c) := by
    funext i; ring
  rw [e]
  refine (l2_avg_add_const_le A _ (add_nonneg hb hc)).trans ?_
  rw [avg_add]
  linarith

theorem l2_ghostAvg_le_one [Fintype R] [DecidableEq D] :
    ∀ (ls : List (LeafSpec X M2)) (out : List (D × R)) (φ : List (Entry S) → ℝ),
      (∀ Γ, φ Γ ≤ 1) → H.ghostAvg ls out φ ≤ 1 := by
  intro ls
  induction ls with
  | nil => intro out φ hφ; rw [ghostAvg]; exact hφ []
  | cons l ls ih =>
    intro out φ hφ
    cases out with
    | nil => rw [ghostAvg]; exact hφ []
    | cons p out =>
      rw [ghostAvg]
      split_ifs
      · exact avg_le zero_le_one fun r _ => avg_le zero_le_one fun o1 _ =>
          avg_le zero_le_one fun o2 _ => ih out _ fun Γ => hφ _
      · exact ih out φ hφ

theorem l2_cnt_mono [Fintype R] [DecidableEq X] (P : Finset X) {A B : Finset S} (h : A ⊆ B) :
    H.cnt P A ≤ H.cnt P B :=
  Finset.card_le_card fun p hp => by
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, h hp.2⟩

theorem l2_cnt_union [Fintype R] [DecidableEq X] (P : Finset X) (A B : Finset S) :
    H.cnt P (A ∪ B) ≤ H.cnt P A + H.cnt P B := by
  classical
  simp only [cnt]
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_union] at hp ⊢
  tauto

theorem l2_cnt_enc1_of_not_mem [Fintype R] [DecidableEq X] {P : Finset X} {x : X} (hx : x ∉ P)
    (r : R) : H.cnt P {H.enc1 (r, x)} = 0 := by
  simp only [cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_product,
    Finset.mem_singleton]
  rintro ⟨r', x'⟩ ⟨_, hx'⟩ he
  have hxx : x' = x := congrArg Prod.snd (H.enc1_inj he)
  exact hx (hxx ▸ hx')

theorem l2_cnt_eq_sum [Fintype R] [DecidableEq X] (P : Finset X) (V : Finset S) :
    H.cnt P V = ∑ x ∈ P, (univ.filter fun r : R => H.enc1 (r, x) ∈ V).card := by
  simp only [cnt, Finset.card_filter]
  rw [Finset.sum_product_right]

theorem l2_cnt_insert [Fintype R] [DecidableEq X] {P : Finset X} {x : X} (hx : x ∉ P)
    (V : Finset S) :
    H.cnt (insert x P) V = (univ.filter fun r : R => H.enc1 (r, x) ∈ V).card + H.cnt P V := by
  rw [H.l2_cnt_eq_sum, H.l2_cnt_eq_sum, Finset.sum_insert hx]

theorem l2_not_mem_hidX [DecidableEq X] {l : LeafSpec X M2} {ls : List (LeafSpec X M2)}
    (h : ((l :: ls).map LeafSpec.x).Nodup) : l.x ∉ hidX ls := by
  rw [List.map_cons, List.nodup_cons] at h
  intro hm
  apply h.1
  simp only [hidX, List.mem_toFinset, List.mem_map, List.mem_filter] at hm
  obtain ⟨a, ⟨ha, _⟩, hax⟩ := hm
  exact List.mem_map.2 ⟨a, ha, hax⟩

theorem l2_hidX_card_le [DecidableEq X] (ls : List (LeafSpec X M2)) :
    (hidX ls).card ≤ hcount ls :=
  (List.toFinset_card_le _).trans (by simp [hcount])

theorem l2_card_enc2_eq_le [DecidableEq C] {Kc : ℕ}
    (hKc : ∀ c : C, (Finset.univ.filter fun s => H.chop s = c).card ≤ Kc) (m : M2) (y : S) :
    (univ.filter fun o : S => y = H.enc2 (H.chop o, m)).card ≤ Kc := by
  by_cases h : ∃ o : S, y = H.enc2 (H.chop o, m)
  · obtain ⟨o0, ho0⟩ := h
    refine (Finset.card_le_card fun o ho => ?_).trans (hKc (H.chop o0))
    rw [Finset.mem_filter] at ho ⊢
    exact ⟨ho.1, congrArg Prod.fst (H.enc2_inj (ho.2.symm.trans ho0))⟩
  · have e : (univ.filter fun o : S => y = H.enc2 (H.chop o, m)) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun o _ ho => h ⟨o, ho⟩
    rw [e, Finset.card_empty]
    exact Nat.zero_le _

theorem l2_card_enc2_mem_le [DecidableEq C] {Kc : ℕ}
    (hKc : ∀ c : C, (Finset.univ.filter fun s => H.chop s = c).card ≤ Kc) (m : M2)
    (T : Finset S) :
    (univ.filter fun o : S => H.enc2 (H.chop o, m) ∈ T).card ≤ T.card * Kc := by
  calc (univ.filter fun o : S => H.enc2 (H.chop o, m) ∈ T).card
      ≤ (T.biUnion fun y => univ.filter fun o : S => y = H.enc2 (H.chop o, m)).card := by
        refine Finset.card_le_card fun o ho => ?_
        rw [Finset.mem_filter] at ho
        exact Finset.mem_biUnion.2 ⟨_, ho.2, Finset.mem_filter.2 ⟨ho.1, rfl⟩⟩
    _ ≤ ∑ y ∈ T, (univ.filter fun o : S => y = H.enc2 (H.chop o, m)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ T, Kc := Finset.sum_le_sum fun y _ => H.l2_card_enc2_eq_le hKc m y
    _ = T.card * Kc := by rw [Finset.sum_const, smul_eq_mul]

theorem l2_sum_cnt_enc2_le [Fintype R] [DecidableEq X] [DecidableEq C] {Kc : ℕ}
    (hKc : ∀ c : C, (Finset.univ.filter fun s => H.chop s = c).card ≤ Kc) (P : Finset X)
    (m : M2) :
    ∑ o : S, H.cnt P {H.enc2 (H.chop o, m)} ≤ Fintype.card R * P.card * Kc := by
  simp only [cnt, Finset.card_filter, Finset.mem_singleton]
  rw [Finset.sum_comm]
  calc ∑ p ∈ univ ×ˢ P, ∑ o : S, (if H.enc1 p = H.enc2 (H.chop o, m) then 1 else 0)
      ≤ ∑ _p ∈ univ ×ˢ P, Kc := Finset.sum_le_sum fun p _ => by
        rw [← Finset.card_filter]
        exact H.l2_card_enc2_eq_le hKc m (H.enc1 p)
    _ = Fintype.card R * P.card * Kc := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_univ, smul_eq_mul]

theorem l2_good {Γacc : List (Entry S)} {t : Trace S} {r : R} {x : X} {m : M2} {o1 o2 : S}
    (e1 : ¬ H.enc1 (r, x) ∈ t.usedIn ∪ (Γacc.map Entry.inp).toFinset)
    (e2 : ¬ (o1 ∈ (Γacc.map Entry.out).toFinset ∪ t.usedOut ∨
      H.enc2 (H.chop o1, m) ∈ (Γacc.map Entry.inp).toFinset ∪ {H.enc1 (r, x)} ∪ t.usedIn))
    (e3 : ¬ o2 ∈ (Γacc.map Entry.out).toFinset ∪ {o1} ∪ t.usedOut)
    (hbad : ¬ GhostBad Γacc t) :
    ¬ GhostBad (Γacc ++ [H.ghost1 r x o1, H.ghost2 o1 m o2]) t := by
  simp only [Finset.mem_union, Finset.mem_singleton, List.mem_toFinset, not_or] at e1 e2 e3
  simp only [GhostBad, Strat.TouchedAny, not_or, not_not, not_exists, not_and] at hbad ⊢
  obtain ⟨hi, ho, hT⟩ := hbad
  have key : ∀ (l : List S) (a b : S), l.Nodup → a ∉ l → b ∉ l → a ≠ b → (l ++ [a, b]).Nodup := by
    intro l a b hl ha hb hab
    refine List.perm_append_comm.nodup_iff.2 ?_
    exact List.nodup_cons.2 ⟨by simp [hab, ha], List.nodup_cons.2 ⟨hb, hl⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.map_append, List.map_cons, List.map_nil, ghost1, ghost2]
    exact key _ _ _ hi e1.2 e2.2.1.1 (fun h => e2.2.1.2 h.symm)
  · simp only [List.map_append, List.map_cons, List.map_nil, ghost1, ghost2]
    exact key _ _ _ ho e2.1.1 e3.1.1 (fun h => e3.1.2 h.symm)
  · intro g hg hTg
    rw [List.mem_append] at hg
    rcases hg with hg | hg
    · exact hT g hg hTg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · rcases hTg with h | h
        · exact e1.1 h
        · exact e2.1.2 h
      · rcases hTg with h | h
        · exact e2.2.2 h
        · exact e3.2 h

/-- One hidden leaf of the bad-event bound: the three ghost draws against the bound for the rest. -/
theorem l2_step [Fintype R] [Nonempty R] [DecidableEq X] [DecidableEq C] [DecidableEq D]
    (F Kc : ℕ) (hF : ∀ d : D, (Finset.univ.filter fun s => H.trunc s = d).card = F)
    (hKc : ∀ c : C, (Finset.univ.filter fun s => H.chop s = c).card ≤ Kc)
    (t : Trace S) (M : ℕ) (hU : t.usedIn.card ≤ M) (hV : t.usedOut.card ≤ M)
    (x : X) (m : M2) (d : D) (P : Finset X) (hxP : x ∉ P)
    (Γacc : List (Entry S)) (hbad : ¬ GhostBad Γacc t) (C0 : ℝ) (hC0 : 0 ≤ C0)
    (G : R → S → S → ℝ) (hG1 : ∀ r o1 o2, G r o1 o2 ≤ 1)
    (hG : ∀ r o1 o2, ¬ GhostBad (Γacc ++ [H.ghost1 r x o1, H.ghost2 o1 m o2]) t →
      G r o1 o2 ≤ (H.cnt P ((Γacc ++ [H.ghost1 r x o1, H.ghost2 o1 m o2]).map Entry.inp).toFinset : ℝ) /
        Fintype.card R + C0) :
    avg univ (fun r : R => avg univ fun o1 : S =>
        avg (univ.filter fun o2 => H.trunc o2 = d) fun o2 => G r o1 o2) ≤
      (((univ.filter fun r : R => H.enc1 (r, x) ∈ t.usedIn).card +
          (univ.filter fun r : R => H.enc1 (r, x) ∈ (Γacc.map Entry.inp).toFinset).card +
          H.cnt P (Γacc.map Entry.inp).toFinset : ℕ) : ℝ) / Fintype.card R + C0 +
        (((Γacc.length + M : ℕ) : ℝ) / Fintype.card S +
          ((Γacc.length + 1 + M : ℕ) : ℝ) * Kc / Fintype.card S +
          (P.card : ℝ) * Kc / Fintype.card S + ((Γacc.length + 1 + M : ℕ) : ℝ) / F) := by
  set Ins := (Γacc.map Entry.inp).toFinset with hIns
  set Outs := (Γacc.map Entry.out).toFinset with hOuts
  have hIc : Ins.card ≤ Γacc.length := (List.toFinset_card_le _).trans (by simp)
  have hOc : Outs.card ≤ Γacc.length := (List.toFinset_card_le _).trans (by simp)
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hcI : 0 ≤ (H.cnt P Ins : ℝ) / Fintype.card R := by positivity
  have hB2 : 0 ≤ ((Γacc.length + 1 + M : ℕ) : ℝ) / F := by positivity
  -- pointwise
  have hpt : ∀ r o1 o2, G r o1 o2 ≤ ind (o2 ∈ Outs ∪ {o1} ∪ t.usedOut) +
      (ind (o1 ∈ Outs ∪ t.usedOut ∨ H.enc2 (H.chop o1, m) ∈ Ins ∪ {H.enc1 (r, x)} ∪ t.usedIn) +
        (H.cnt P {H.enc2 (H.chop o1, m)} : ℝ) / Fintype.card R +
        (ind (H.enc1 (r, x) ∈ t.usedIn ∪ Ins) + (H.cnt P Ins : ℝ) / Fintype.card R + C0)) := by
    intro r o1 o2
    have h0 : 0 ≤ (H.cnt P {H.enc2 (H.chop o1, m)} : ℝ) / Fintype.card R := by positivity
    have i1 := ind_nonneg (o2 ∈ Outs ∪ {o1} ∪ t.usedOut)
    have i2 := ind_nonneg
      (o1 ∈ Outs ∪ t.usedOut ∨ H.enc2 (H.chop o1, m) ∈ Ins ∪ {H.enc1 (r, x)} ∪ t.usedIn)
    have i3 := ind_nonneg (H.enc1 (r, x) ∈ t.usedIn ∪ Ins)
    have hg1 := hG1 r o1 o2
    by_cases e3 : o2 ∈ Outs ∪ {o1} ∪ t.usedOut
    · rw [ind_pos e3]; linarith
    by_cases e2 : o1 ∈ Outs ∪ t.usedOut ∨ H.enc2 (H.chop o1, m) ∈ Ins ∪ {H.enc1 (r, x)} ∪ t.usedIn
    · rw [ind_pos e2]; linarith
    by_cases e1 : H.enc1 (r, x) ∈ t.usedIn ∪ Ins
    · rw [ind_pos e1]; linarith
    have hgood := H.l2_good e1 e2 e3 hbad
    have hc : H.cnt P ((Γacc ++ [H.ghost1 r x o1, H.ghost2 o1 m o2]).map Entry.inp).toFinset ≤
        H.cnt P Ins + H.cnt P {H.enc2 (H.chop o1, m)} := by
      calc H.cnt P ((Γacc ++ [H.ghost1 r x o1, H.ghost2 o1 m o2]).map Entry.inp).toFinset
          ≤ H.cnt P (Ins ∪ {H.enc1 (r, x)} ∪ {H.enc2 (H.chop o1, m)}) := by
            refine H.l2_cnt_mono P fun y hy => ?_
            simp only [hIns, List.map_append, List.map_cons, List.map_nil, List.mem_toFinset,
              List.mem_append, List.mem_cons, List.not_mem_nil, Finset.mem_union,
              Finset.mem_singleton, ghost1, ghost2, or_false] at hy ⊢
            tauto
        _ ≤ H.cnt P (Ins ∪ {H.enc1 (r, x)}) + H.cnt P {H.enc2 (H.chop o1, m)} :=
            H.l2_cnt_union P _ _
        _ ≤ H.cnt P Ins + H.cnt P {H.enc1 (r, x)} + H.cnt P {H.enc2 (H.chop o1, m)} :=
            Nat.add_le_add_right (H.l2_cnt_union P _ _) _
        _ = H.cnt P Ins + H.cnt P {H.enc2 (H.chop o1, m)} := by
            rw [H.l2_cnt_enc1_of_not_mem hxP r, Nat.add_zero]
    have hc' : (H.cnt P ((Γacc ++ [H.ghost1 r x o1, H.ghost2 o1 m o2]).map Entry.inp).toFinset : ℝ) /
        Fintype.card R ≤ (H.cnt P Ins : ℝ) / Fintype.card R +
          (H.cnt P {H.enc2 (H.chop o1, m)} : ℝ) / Fintype.card R := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hc) hR.le
    linarith [hG r o1 o2 hgood]
  -- the second reply
  have h2 : ∀ r o1, avg (univ.filter fun o2 => H.trunc o2 = d) (fun o2 => G r o1 o2) ≤
      ((Γacc.length + 1 + M : ℕ) : ℝ) / F +
      (ind (o1 ∈ Outs ∪ t.usedOut ∨ H.enc2 (H.chop o1, m) ∈ Ins ∪ {H.enc1 (r, x)} ∪ t.usedIn) +
        (H.cnt P {H.enc2 (H.chop o1, m)} : ℝ) / Fintype.card R +
        (ind (H.enc1 (r, x) ∈ t.usedIn ∪ Ins) + (H.cnt P Ins : ℝ) / Fintype.card R + C0)) := by
    intro r o1
    refine (avg_le_of_le_ind_add _ _ (fun o2 => o2 ∈ Outs ∪ {o1} ∪ t.usedOut) _
      (add_nonneg (add_nonneg (ind_nonneg _) (by positivity))
        (add_nonneg (add_nonneg (ind_nonneg _) hcI) hC0)) fun o2 _ => hpt r o1 o2).trans ?_
    rw [add_le_add_iff_right]
    refine (avg_ind_mem_le _ (Outs ∪ {o1} ∪ t.usedOut) _ fun o2 _ h => h).trans ?_
    rw [hF d]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    have h1 := Finset.card_union_le (Outs ∪ {o1}) t.usedOut
    have h2 := Finset.card_union_le Outs {o1}
    rw [Finset.card_singleton] at h2
    exact_mod_cast (show (Outs ∪ {o1} ∪ t.usedOut).card ≤ Γacc.length + 1 + M by omega)
  -- the first reply
  have hE1 : ∀ r, avg univ (fun o1 : S =>
      ind (o1 ∈ Outs ∪ t.usedOut ∨ H.enc2 (H.chop o1, m) ∈ Ins ∪ {H.enc1 (r, x)} ∪ t.usedIn)) ≤
      ((Γacc.length + M : ℕ) : ℝ) / Fintype.card S +
        ((Γacc.length + 1 + M : ℕ) : ℝ) * Kc / Fintype.card S := by
    intro r
    refine (avg_ind_mem_le univ ((Outs ∪ t.usedOut) ∪
      univ.filter fun o1 => H.enc2 (H.chop o1, m) ∈ Ins ∪ {H.enc1 (r, x)} ∪ t.usedIn) _
      fun o1 _ h => ?_).trans ?_
    · rcases h with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    · rw [Finset.card_univ, ← add_div]
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
      have hA := Finset.card_union_le (Outs ∪ t.usedOut)
        (univ.filter fun o1 => H.enc2 (H.chop o1, m) ∈ Ins ∪ {H.enc1 (r, x)} ∪ t.usedIn)
      have hB := Finset.card_union_le Outs t.usedOut
      have hC := H.l2_card_enc2_mem_le hKc m (Ins ∪ {H.enc1 (r, x)} ∪ t.usedIn)
      have hD : (Ins ∪ {H.enc1 (r, x)} ∪ t.usedIn).card ≤ Γacc.length + 1 + M := by
        have h1 := Finset.card_union_le (Ins ∪ {H.enc1 (r, x)}) t.usedIn
        have h2 := Finset.card_union_le Ins {H.enc1 (r, x)}
        rw [Finset.card_singleton] at h2
        omega
      exact_mod_cast hA.trans (Nat.add_le_add (hB.trans (Nat.add_le_add hOc hV))
        (hC.trans (Nat.mul_le_mul hD le_rfl)))
  -- the count of the second input
  have hcw : avg univ (fun o1 : S => (H.cnt P {H.enc2 (H.chop o1, m)} : ℝ) / Fintype.card R) ≤
      (P.card : ℝ) * Kc / Fintype.card S := by
    unfold avg
    rw [Finset.card_univ, ← Finset.sum_div]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    rw [div_le_iff₀ hR]
    have hs := H.l2_sum_cnt_enc2_le hKc P m
    calc ∑ o1 : S, (H.cnt P {H.enc2 (H.chop o1, m)} : ℝ)
        = ((∑ o1 : S, H.cnt P {H.enc2 (H.chop o1, m)} : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ ((Fintype.card R * P.card * Kc : ℕ) : ℝ) := by exact_mod_cast hs
      _ = (P.card : ℝ) * Kc * Fintype.card R := by push_cast; ring
  -- the salt
  have hEr : avg univ (fun r : R => ind (H.enc1 (r, x) ∈ t.usedIn ∪ Ins)) ≤
      (((univ.filter fun r : R => H.enc1 (r, x) ∈ t.usedIn).card +
        (univ.filter fun r : R => H.enc1 (r, x) ∈ Ins).card : ℕ) : ℝ) / Fintype.card R := by
    classical
    refine (avg_ind_mem_le univ ((univ.filter fun r : R => H.enc1 (r, x) ∈ t.usedIn) ∪
      (univ.filter fun r : R => H.enc1 (r, x) ∈ Ins)) _ fun r _ h => ?_).trans ?_
    · rw [Finset.mem_union] at h
      rcases h with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    · rw [Finset.card_univ]
      exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_union_le _ _)
        (Nat.cast_nonneg _)
  have h1 : ∀ r, avg univ (fun o1 =>
      avg (univ.filter fun o2 => H.trunc o2 = d) fun o2 => G r o1 o2) ≤
      ind (H.enc1 (r, x) ∈ t.usedIn ∪ Ins) +
        ((((Γacc.length + M : ℕ) : ℝ) / Fintype.card S +
            ((Γacc.length + 1 + M : ℕ) : ℝ) * Kc / Fintype.card S) +
          (P.card : ℝ) * Kc / Fintype.card S + ((Γacc.length + 1 + M : ℕ) : ℝ) / F +
          (H.cnt P Ins : ℝ) / Fintype.card R + C0) := by
    intro r
    refine (avg_mono fun o1 _ => h2 r o1).trans ?_
    refine (l2_avg_split univ _ _ _ _ _ _ hB2
      (add_nonneg (add_nonneg (ind_nonneg _) hcI) hC0) (hE1 r) hcw).trans (le_of_eq ?_)
    ring
  have hK : 0 ≤ (((Γacc.length + M : ℕ) : ℝ) / Fintype.card S +
            ((Γacc.length + 1 + M : ℕ) : ℝ) * Kc / Fintype.card S) +
          (P.card : ℝ) * Kc / Fintype.card S + ((Γacc.length + 1 + M : ℕ) : ℝ) / F +
          (H.cnt P Ins : ℝ) / Fintype.card R + C0 := by
    have : 0 ≤ (((Γacc.length + M : ℕ) : ℝ) / Fintype.card S +
            ((Γacc.length + 1 + M : ℕ) : ℝ) * Kc / Fintype.card S) +
          (P.card : ℝ) * Kc / Fintype.card S + ((Γacc.length + 1 + M : ℕ) : ℝ) / F +
          (H.cnt P Ins : ℝ) / Fintype.card R := by positivity
    linarith
  refine (avg_mono fun r _ => h1 r).trans ((l2_avg_add_const_le _ _ hK).trans ?_)
  have e : ((((univ.filter fun r : R => H.enc1 (r, x) ∈ t.usedIn).card +
        (univ.filter fun r : R => H.enc1 (r, x) ∈ Ins).card : ℕ) : ℝ) / Fintype.card R) +
        (H.cnt P Ins : ℝ) / Fintype.card R =
      (((univ.filter fun r : R => H.enc1 (r, x) ∈ t.usedIn).card +
          (univ.filter fun r : R => H.enc1 (r, x) ∈ Ins).card + H.cnt P Ins : ℕ) : ℝ) /
        Fintype.card R := by
    push_cast; ring
  linarith

/-- The bad event for a fixed final table `t`: what is left besides a constant per hidden
leaf is a used hidden first-call input (in the table or among the earlier ghosts' inputs). -/
theorem ghost_bad_le [Fintype R] [Nonempty R] [DecidableEq D] [DecidableEq X] [DecidableEq C]
    (F Kc : ℕ) (hF : ∀ d : D, (Finset.univ.filter fun s => H.trunc s = d).card = F)
    (hKc : ∀ c : C, (Finset.univ.filter fun s => H.chop s = c).card ≤ Kc)
    (t : Trace S) (M N : ℕ) (hU : t.usedIn.card ≤ M) (hV : t.usedOut.card ≤ M) :
    ∀ (ls : List (LeafSpec X M2)) (out : List (D × R)) (Γacc : List (Entry S)),
      (ls.map LeafSpec.x).Nodup → ¬ GhostBad Γacc t → Γacc.length + 2 * hcount ls ≤ 2 * N →
      H.ghostAvg ls out (fun Γ => ind (GhostBad (Γacc ++ Γ) t)) ≤
        ((H.cnt (hidX ls) t.usedIn + H.cnt (hidX ls) (Γacc.map Entry.inp).toFinset : ℕ) : ℝ) /
            Fintype.card R +
          (hcount ls : ℝ) * ((2 * N + M : ℕ) : ℝ) *
            (1 / (Fintype.card S : ℝ) + Kc / (Fintype.card S : ℝ) + 1 / (F : ℝ)) := by
  intro ls
  induction ls with
  | nil =>
    intro out Γacc _ hbad _
    rw [ghostAvg]
    simp only [List.append_nil, ind_neg hbad]
    positivity
  | cons l ls ih =>
    intro out Γacc hnd hbad hlen
    have hnd' : (ls.map LeafSpec.x).Nodup := by
      rw [List.map_cons, List.nodup_cons] at hnd
      exact hnd.2
    cases out with
    | nil =>
      rw [ghostAvg]
      simp only [List.append_nil, ind_neg hbad]
      positivity
    | cons p out =>
      by_cases hl : l.hidden = true
      · have hc : hcount (l :: ls) = hcount ls + 1 := by simp [hcount, hl]
        have hX : hidX (l :: ls) = insert l.x (hidX ls) := by simp [hidX, hl]
        have hxP := l2_not_mem_hidX hnd
        have hPc := l2_hidX_card_le ls
        rw [ghostAvg]
        simp only [hl, ↓reduceIte]
        refine (H.l2_step F Kc hF hKc t M hU hV l.x l.m p.1 (hidX ls) hxP Γacc hbad
          ((H.cnt (hidX ls) t.usedIn : ℝ) / Fintype.card R + (hcount ls : ℝ) * ((2 * N + M : ℕ) : ℝ) *
            (1 / (Fintype.card S : ℝ) + Kc / (Fintype.card S : ℝ) + 1 / (F : ℝ))) (by positivity)
          (fun r o1 o2 => H.ghostAvg ls out fun Γ =>
            ind (GhostBad (Γacc ++ H.ghost1 r l.x o1 :: H.ghost2 o1 l.m o2 :: Γ) t))
          (fun r o1 o2 => H.l2_ghostAvg_le_one ls out _ fun _ => ind_le_one _) ?_).trans ?_
        · intro r o1 o2 hgood
          have hih := ih out (Γacc ++ [H.ghost1 r l.x o1, H.ghost2 o1 l.m o2]) hnd' hgood (by
            rw [hc] at hlen
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega)
          simp only [List.append_assoc, List.cons_append, List.nil_append] at hih
          refine hih.trans (le_of_eq ?_)
          push_cast
          ring
        · rw [hc, hX, H.l2_cnt_insert hxP, H.l2_cnt_insert hxP]
          rw [hc] at hlen
          have hS0 : (0 : ℝ) ≤ Fintype.card S := Nat.cast_nonneg _
          have hF0 : (0 : ℝ) ≤ F := Nat.cast_nonneg _
          have ha : ((Γacc.length + M : ℕ) : ℝ) / Fintype.card S ≤
              ((2 * N + M : ℕ) : ℝ) / Fintype.card S :=
            div_le_div_of_nonneg_right (by exact_mod_cast (show Γacc.length + M ≤ 2 * N + M by omega)) hS0
          have hb : ((Γacc.length + 1 + M : ℕ) : ℝ) * Kc / Fintype.card S +
              ((hidX ls).card : ℝ) * Kc / Fintype.card S ≤
              ((2 * N + M : ℕ) : ℝ) * Kc / Fintype.card S := by
            rw [← add_div, ← add_mul]
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
              (by exact_mod_cast (show Γacc.length + 1 + M + (hidX ls).card ≤ 2 * N + M by omega))
              (Nat.cast_nonneg _)) hS0
          have hd : ((Γacc.length + 1 + M : ℕ) : ℝ) / F ≤ ((2 * N + M : ℕ) : ℝ) / F :=
            div_le_div_of_nonneg_right
              (by exact_mod_cast (show Γacc.length + 1 + M ≤ 2 * N + M by omega)) hF0
          have hε : ((2 * N + M : ℕ) : ℝ) *
              (1 / (Fintype.card S : ℝ) + Kc / (Fintype.card S : ℝ) + 1 / (F : ℝ)) =
              ((2 * N + M : ℕ) : ℝ) / Fintype.card S + ((2 * N + M : ℕ) : ℝ) * Kc / Fintype.card S +
                ((2 * N + M : ℕ) : ℝ) / F := by ring
          have hsplit : ((((univ.filter fun r : R => H.enc1 (r, l.x) ∈ t.usedIn).card +
                (univ.filter fun r : R => H.enc1 (r, l.x) ∈ (Γacc.map Entry.inp).toFinset).card +
                H.cnt (hidX ls) (Γacc.map Entry.inp).toFinset : ℕ) : ℝ) / Fintype.card R) +
              (H.cnt (hidX ls) t.usedIn : ℝ) / Fintype.card R =
              ((((univ.filter fun r : R => H.enc1 (r, l.x) ∈ t.usedIn).card +
                H.cnt (hidX ls) t.usedIn +
                ((univ.filter fun r : R => H.enc1 (r, l.x) ∈ (Γacc.map Entry.inp).toFinset).card +
                H.cnt (hidX ls) (Γacc.map Entry.inp).toFinset) : ℕ) : ℝ) / Fintype.card R) := by
            push_cast; ring
          have hcast : ((hcount ls + 1 : ℕ) : ℝ) = (hcount ls : ℝ) + 1 := by push_cast; ring
          rw [hcast]
          nlinarith [hε]
      · have hc : hcount (l :: ls) = hcount ls := by simp [hcount, hl]
        have hX : hidX (l :: ls) = hidX ls := by simp [hidX, hl]
        rw [ghostAvg]
        simp only [hl, Bool.false_eq_true, ↓reduceIte]
        rw [hc, hX]
        exact ih out Γacc hnd' hbad (by rw [hc] at hlen; exact hlen)

/-! ### Helpers for the counts of used first-call inputs -/

theorem l34_usedIn_stepF (t : Trace S) (x y : S) : (t.stepF x y).usedIn ⊆ insert x t.usedIn := by
  unfold Trace.stepF
  split_ifs
  · exact subset_insert _ _
  · intro z hz
    simp only [Trace.mem_usedIn, List.mem_cons] at hz
    obtain ⟨e, he | he, rfl⟩ := hz
    · subst he; exact mem_insert_self _ _
    · exact mem_insert_of_mem (Trace.mem_usedIn.2 ⟨e, he, rfl⟩)

theorem l34_usedIn_stepI (t : Trace S) (x y : S) : (t.stepI x y).usedIn ⊆ insert x t.usedIn := by
  unfold Trace.stepI
  split_ifs
  · exact subset_insert _ _
  · intro z hz
    simp only [Trace.mem_usedIn, List.mem_cons] at hz
    obtain ⟨e, he | he, rfl⟩ := hz
    · subst he; exact mem_insert_self _ _
    · exact mem_insert_of_mem (Trace.mem_usedIn.2 ⟨e, he, rfl⟩)

theorem l34_cnt_mono [Fintype R] [DecidableEq X] (P : Finset X) {U V : Finset S} (h : U ⊆ V) :
    H.cnt P U ≤ H.cnt P V :=
  card_le_card fun p hp => by
    simp only [mem_filter] at hp ⊢
    exact ⟨hp.1, h hp.2⟩

theorem l34_cnt_insert_le [Fintype R] [DecidableEq X] (P : Finset X) (U : Finset S) (y : S) :
    H.cnt P (insert y U) ≤ H.cnt P U + ((univ ×ˢ P).filter fun p => H.enc1 p = y).card := by
  classical
  unfold cnt
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro p hp
  simp only [mem_filter, mem_insert, mem_union] at hp ⊢
  rcases hp with ⟨hp, h | h⟩
  · exact Or.inr ⟨hp, h⟩
  · exact Or.inl ⟨hp, h⟩

theorem l34_cnt_stepF_le [Fintype R] [DecidableEq X] (P : Finset X) (t : Trace S) (x y : S) :
    H.cnt P (t.stepF x y).usedIn ≤
      H.cnt P t.usedIn + ((univ ×ˢ P).filter fun p => H.enc1 p = x).card :=
  (H.l34_cnt_mono P (l34_usedIn_stepF t x y)).trans (H.l34_cnt_insert_le P _ x)

theorem l34_cnt_stepI_le [Fintype R] [DecidableEq X] (P : Finset X) (t : Trace S) (x y : S) :
    H.cnt P (t.stepI x y).usedIn ≤
      H.cnt P t.usedIn + ((univ ×ˢ P).filter fun p => H.enc1 p = x).card :=
  (H.l34_cnt_mono P (l34_usedIn_stepI t x y)).trans (H.l34_cnt_insert_le P _ x)

theorem l34_fib_le_one [Fintype R] [DecidableEq X] (P : Finset X) (y : S) :
    ((univ ×ˢ P).filter fun p => H.enc1 p = y).card ≤ 1 := by
  refine card_le_one.2 fun a ha b hb => ?_
  simp only [mem_filter] at ha hb
  exact H.enc1_inj (ha.2.trans hb.2.symm)

theorem l34_fib_eq_zero [Fintype R] [DecidableEq X] (shape : S → Prop)
    (hshape : ∀ r x, shape (H.enc1 (r, x))) (P : Finset X) (y : S) (hy : ¬ shape y) :
    ((univ ×ˢ P).filter fun p => H.enc1 p = y).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro ⟨r, x⟩ _ h
  exact hy (h ▸ hshape r x)

theorem l34_sum_fib_le [Fintype R] [DecidableEq X] (P : Finset X) (A : Finset S) :
    ∑ y ∈ A, ((univ ×ˢ P).filter fun p => H.enc1 p = y).card ≤ Fintype.card R * P.card := by
  have h : ∀ y ∈ A, ((univ ×ˢ P).filter fun p => H.enc1 p = y).card =
      ∑ p ∈ univ ×ˢ P, if H.enc1 p = y then 1 else 0 := fun y _ => card_filter _ _
  rw [sum_congr rfl h, sum_comm]
  calc ∑ p ∈ univ ×ˢ P, ∑ y ∈ A, (if H.enc1 p = y then 1 else 0)
        ≤ ∑ _p ∈ univ ×ˢ P, 1 := sum_le_sum fun p _ => by
          rw [sum_ite_eq]
          split_ifs <;> simp
    _ = Fintype.card R * P.card := by simp [card_product]

theorem l34_avg_le_div {ι : Type} (A : Finset ι) (g : ι → ℝ) (K d : ℝ)
    (hg : ∀ i ∈ A, 0 ≤ g i) (hK : ∑ i ∈ A, g i ≤ K) (hd : 0 < d) (hdA : d ≤ A.card) :
    avg A g ≤ K / d := by
  unfold avg
  have hK0 : 0 ≤ K := (sum_nonneg hg).trans hK
  exact (div_le_div_of_nonneg_right hK (Nat.cast_nonneg _)).trans
    (div_le_div_of_nonneg_left hK0 hd hdA)

theorem l34_card_free_ge (t : Trace S) (ht : t.WF) (M : ℕ) (hM : M < Fintype.card S)
    (hl : t.length ≤ M) :
    (Fintype.card S : ℝ) - M ≤ (t.freeIn.card : ℝ) ∧ (Fintype.card S : ℝ) - M ≤ (t.freeOut.card : ℝ) := by
  rw [ht.card_freeIn, ht.card_freeOut, Nat.cast_sub (by omega)]
  have : (t.length : ℝ) ≤ M := by exact_mod_cast hl
  constructor <;> linarith

/-- Second stage: new used hidden first-call inputs come from shaped forward queries or from
inverse answers. -/
theorem a2_cnt_le [Fintype R] [DecidableEq X] (shape : S → Prop)
    (hshape : ∀ r x, shape (H.enc1 (r, x))) (P : Finset X) (M : ℕ) (hM : M < Fintype.card S)
    {α : Type} (st : Strat S α) (Q q : ℕ) (hQ : st.QB Q) (hq : st.FQB shape q) (s : PState S)
    (hs : s.trace.WF) (hlen : s.trace.length + Q ≤ M) :
    st.exp s (fun _ s' => (H.cnt P s'.trace.usedIn : ℝ)) ≤
      (H.cnt P s.trace.usedIn : ℝ) + q +
        (Q : ℝ) * ((Fintype.card R * P.card : ℕ) / ((Fintype.card S : ℝ) - M)) := by
  have hpos : (0 : ℝ) < (Fintype.card S : ℝ) - M := by
    have : (M : ℝ) < Fintype.card S := by exact_mod_cast hM
    linarith
  have hc0 : 0 ≤ ((Fintype.card R * P.card : ℕ) : ℝ) / ((Fintype.card S : ℝ) - M) :=
    div_nonneg (Nat.cast_nonneg _) hpos.le
  induction st generalizing s Q q with
  | done a =>
    simp only [Strat.exp]
    have h1 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have h2 := mul_nonneg (Nat.cast_nonneg Q) hc0
    linarith
  | fwd x k ih =>
    cases hQ with
    | fwd _ _ n hk =>
    simp only [Strat.exp]
    refine avg_le (add_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) hc0)) fun y hy => ?_
    have hwf := hs.stepF hy
    have hl := Trace.length_stepF_le s.trace x y
    have hcnt := H.l34_cnt_stepF_le P s.trace x y
    have e : (((n + 1 : ℕ) : ℝ)) * (((Fintype.card R * P.card : ℕ) : ℝ) / ((Fintype.card S : ℝ) - M)) =
        n * (((Fintype.card R * P.card : ℕ) : ℝ) / ((Fintype.card S : ℝ) - M)) +
          ((Fintype.card R * P.card : ℕ) : ℝ) / ((Fintype.card S : ℝ) - M) := by
      push_cast; ring
    rw [e]
    by_cases hx : shape x
    · obtain ⟨hq0, hq'⟩ := hq.1 hx
      have h1 := ih y n (q - 1) (hk y) (hq' y) ⟨s.trace.stepF x y, s.count + 1⟩ hwf
        (by simp only; omega)
      have hf := H.l34_fib_le_one P x
      have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      simp only at h1
      rw [hcast] at h1
      have h2 : (H.cnt P (s.trace.stepF x y).usedIn : ℝ) ≤ H.cnt P s.trace.usedIn + 1 := by
        exact_mod_cast hcnt.trans (by omega)
      linarith
    · have h1 := ih y n q (hk y) (hq.2 hx y) ⟨s.trace.stepF x y, s.count + 1⟩ hwf
        (by simp only; omega)
      have hf := H.l34_fib_eq_zero shape hshape P x hx
      simp only at h1
      have h2 : (H.cnt P (s.trace.stepF x y).usedIn : ℝ) ≤ H.cnt P s.trace.usedIn := by
        exact_mod_cast hcnt.trans (by omega)
      linarith
  | inv y k ih =>
    cases hQ with
    | inv _ _ n hk =>
    simp only [Strat.exp]
    have e : (((n + 1 : ℕ) : ℝ)) * (((Fintype.card R * P.card : ℕ) : ℝ) / ((Fintype.card S : ℝ) - M)) =
        n * (((Fintype.card R * P.card : ℕ) : ℝ) / ((Fintype.card S : ℝ) - M)) +
          ((Fintype.card R * P.card : ℕ) : ℝ) / ((Fintype.card S : ℝ) - M) := by
      push_cast; ring
    rw [e]
    have hB0 : 0 ≤ (H.cnt P s.trace.usedIn : ℝ) + q +
        n * (((Fintype.card R * P.card : ℕ) : ℝ) / ((Fintype.card S : ℝ) - M)) :=
      add_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (mul_nonneg (Nat.cast_nonneg _) hc0)
    have step : ∀ x ∈ s.trace.invAns y,
        (k x).exp ⟨s.trace.stepI x y, s.count + 1⟩ (fun _ s' => (H.cnt P s'.trace.usedIn : ℝ)) ≤
          ((H.cnt P s.trace.usedIn : ℝ) + q +
            n * (((Fintype.card R * P.card : ℕ) : ℝ) / ((Fintype.card S : ℝ) - M))) +
            (((univ ×ˢ P).filter fun p => H.enc1 p = x).card : ℝ) := by
      intro x hx
      have h1 := ih x n q (hk x) (hq x) ⟨s.trace.stepI x y, s.count + 1⟩ (hs.stepI hx)
        (by have := Trace.length_stepI_le s.trace x y; simp only; omega)
      simp only at h1
      have h2 : (H.cnt P (s.trace.stepI x y).usedIn : ℝ) ≤
          H.cnt P s.trace.usedIn + (((univ ×ˢ P).filter fun p => H.enc1 p = x).card : ℝ) := by
        exact_mod_cast H.l34_cnt_stepI_le P s.trace x y
      linarith
    by_cases hy : y ∈ s.trace.usedOut
    · refine avg_le (by linarith) fun x hx => ?_
      have hst : s.trace.stepI x y = s.trace := by simp [Trace.stepI, hy]
      have h1 := ih x n q (hk x) (hq x) ⟨s.trace.stepI x y, s.count + 1⟩ (hs.stepI hx)
        (by have := Trace.length_stepI_le s.trace x y; simp only; omega)
      simp only [hst] at h1
      rw [hst]
      linarith
    · have hA : s.trace.invAns y = s.trace.freeIn := by simp [Trace.invAns, hy]
      have hfree := (l34_card_free_ge s.trace hs M hM (by omega)).1
      have hne : s.trace.freeIn.Nonempty := by
        rw [← card_pos]
        have : (0 : ℝ) < s.trace.freeIn.card := lt_of_lt_of_le hpos hfree
        exact_mod_cast this
      rw [hA] at step ⊢
      refine (avg_mono step).trans ?_
      rw [avg_add, avg_const hne]
      have hfib : avg s.trace.freeIn (fun x => (((univ ×ˢ P).filter fun p => H.enc1 p = x).card : ℝ)) ≤
          ((Fintype.card R * P.card : ℕ) : ℝ) / ((Fintype.card S : ℝ) - M) :=
        l34_avg_le_div _ _ _ _ (fun _ _ => Nat.cast_nonneg _)
          (by rw [← Nat.cast_sum]; exact_mod_cast H.l34_sum_fib_le P _) hpos hfree
      linarith
  | rand m k ih =>
    cases hQ with
    | rand _ _ _ hk =>
    simp only [Strat.exp]
    exact avg_le (add_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) hc0)) fun i _ => ih i Q q (hk i) (hq i) s hs hlen

theorem l34_view_cons (l : LeafSpec X M2) (ls : List (LeafSpec X M2)) (p : D × R)
    (out : List (D × R)) :
    view (l :: ls) (p :: out) = (p.1, if l.hidden then none else some p.2) :: view ls out := rfl

theorem l34_openX_sub [DecidableEq X] (l : LeafSpec X M2) (ls : List (LeafSpec X M2)) :
    openX ls ⊆ openX (l :: ls) := by
  intro y hy
  simp only [openX, List.mem_toFinset, List.mem_map, List.mem_filter] at hy ⊢
  obtain ⟨l', ⟨h1, h2⟩, rfl⟩ := hy
  exact ⟨l', ⟨List.mem_cons_of_mem _ h1, h2⟩, rfl⟩

theorem l34_openX_hidden [DecidableEq X] (l : LeafSpec X M2) (ls : List (LeafSpec X M2))
    (hh : l.hidden = true) : openX (l :: ls) = openX ls := by
  simp [openX, hh]

theorem l34_openX_open [DecidableEq X] (l : LeafSpec X M2) (ls : List (LeafSpec X M2))
    (hh : l.hidden = false) : openX (l :: ls) = insert l.x (openX ls) := by
  simp [openX, hh]

theorem l34_not_mem_openX [DecidableEq X] (ls : List (LeafSpec X M2)) (x : X)
    (hx : x ∉ ls.map LeafSpec.x) : x ∉ openX ls := by
  intro h
  simp only [openX, List.mem_toFinset, List.mem_map, List.mem_filter] at h
  obtain ⟨l', ⟨h1, _⟩, rfl⟩ := h
  exact hx (List.mem_map.2 ⟨l', h1, rfl⟩)

theorem l34_fib_enc1_eq_zero [Fintype R] [DecidableEq X] (A : Finset X) (r : R) (x : X)
    (hx : x ∉ A) : ((univ ×ˢ A).filter fun p => H.enc1 p = H.enc1 (r, x)).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p hp h
  have := H.enc1_inj h
  subst this
  exact hx (mem_product.1 hp).2

theorem l34_sum_fib_enc2_le [Fintype R] [DecidableEq X] [DecidableEq C] (Kc : ℕ)
    (hKc : ∀ c : C, (Finset.univ.filter fun s => H.chop s = c).card ≤ Kc)
    (A : Finset X) (m : M2) (T : Finset S) :
    ∑ o ∈ T, ((univ ×ˢ A).filter fun p => H.enc1 p = H.enc2 (H.chop o, m)).card ≤
      Fintype.card R * A.card * Kc := by
  have h : ∀ o ∈ T, ((univ ×ˢ A).filter fun p => H.enc1 p = H.enc2 (H.chop o, m)).card =
      ∑ p ∈ univ ×ˢ A, if H.enc1 p = H.enc2 (H.chop o, m) then 1 else 0 :=
    fun o _ => card_filter _ _
  rw [sum_congr rfl h, sum_comm]
  calc ∑ p ∈ univ ×ˢ A, ∑ o ∈ T, (if H.enc1 p = H.enc2 (H.chop o, m) then 1 else 0)
        ≤ ∑ _p ∈ univ ×ˢ A, Kc := sum_le_sum fun p _ => by
          rw [← card_filter]
          by_cases hex : ∃ o ∈ T, H.enc1 p = H.enc2 (H.chop o, m)
          · obtain ⟨o0, _, h0⟩ := hex
            refine (card_le_card fun o ho => ?_).trans (hKc (H.chop o0))
            simp only [mem_filter, mem_univ, true_and] at ho ⊢
            exact (Prod.mk.inj (H.enc2_inj (ho.2.symm.trans h0))).1
          · have he : T.filter (fun o => H.enc1 p = H.enc2 (H.chop o, m)) = ∅ :=
              filter_eq_empty_iff.2 fun o ho h => hex ⟨o, ho, h⟩
            rw [he, card_empty]
            exact Nat.zero_le _
    _ = Fintype.card R * A.card * Kc := by simp [card_product, mul_assoc]

theorem l34_cnt_open_cons [Fintype R] [DecidableEq X] (O : Finset X) (x : X) (hx : x ∉ O)
    (U : Finset S) :
    (univ.filter fun r : R => H.enc1 (r, x) ∈ U).card + H.cnt O U ≤ H.cnt (insert x O) U := by
  classical
  unfold cnt
  rw [← card_image_of_injective (univ.filter fun r : R => H.enc1 (r, x) ∈ U)
    (f := fun r => (r, x)) (fun a b h => (Prod.mk.inj h).1)]
  rw [← card_union_of_disjoint]
  · refine card_le_card fun p hp => ?_
    simp only [mem_union, mem_image, mem_filter, mem_univ, true_and, mem_product,
      mem_insert] at hp ⊢
    rcases hp with ⟨r, hr, rfl⟩ | ⟨hp, hpU⟩
    · exact ⟨Or.inl rfl, hr⟩
    · exact ⟨Or.inr hp, hpU⟩
  · rw [disjoint_left]
    intro p hp hp'
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_product] at hp hp'
    obtain ⟨r, _, rfl⟩ := hp
    exact hx hp'.1

/-- The ideal run: used hidden first-call inputs (hidden `x` in `P`). The opened leaves of
`rem` pay with their own salts for first-call inputs already in the table. -/
theorem ideal_cnt_le [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [DecidableEq X]
    [DecidableEq C] (Kc : ℕ) (hKc : ∀ c : C, (Finset.univ.filter fun s => H.chop s = c).card ≤ Kc)
    (shape : S → Prop) (hshape : ∀ r x, shape (H.enc1 (r, x))) (P : Finset X) (N M Q2 q2 : ℕ)
    (hM : M < Fintype.card S) :
    ∀ (rem : List (LeafSpec X M2)) (B : List (D × Option R) → Strat S Bool) (t : Trace S) (c : ℕ),
      (rem.map LeafSpec.x).Nodup → (∀ l ∈ rem, l.hidden = false → l.x ∉ P) →
      P.card + (openX rem).card ≤ N → t.WF → t.length + 2 * rem.length + Q2 ≤ M →
      (∀ v, (B v).QB Q2 ∧ (B v).FQB shape q2) →
      (H.layerIdeal rem).exp ⟨t, c⟩ (fun out s => (B (view rem out)).exp s fun _ s' =>
          min 1 ((H.cnt P s'.trace.usedIn : ℝ) / Fintype.card R)) ≤
        ((H.cnt P t.usedIn + H.cnt (openX rem) t.usedIn : ℕ) : ℝ) / Fintype.card R +
          (rem.length : ℝ) * (N * Kc / ((Fintype.card S : ℝ) - M)) + (q2 : ℝ) / Fintype.card R +
          (Q2 : ℝ) * (N / ((Fintype.card S : ℝ) - M)) := by
  have hpos : (0 : ℝ) < (Fintype.card S : ℝ) - M := by
    have : (M : ℝ) < Fintype.card S := by exact_mod_cast hM
    linarith
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have ha0 : (0 : ℝ) ≤ N * Kc / ((Fintype.card S : ℝ) - M) := div_nonneg (by positivity) hpos.le
  have hb0 : (0 : ℝ) ≤ N / ((Fintype.card S : ℝ) - M) := div_nonneg (by positivity) hpos.le
  have hnn : ∀ u k : ℕ, (0 : ℝ) ≤ (u : ℝ) / Fintype.card R +
      (k : ℝ) * (N * Kc / ((Fintype.card S : ℝ) - M)) + (q2 : ℝ) / Fintype.card R +
      (Q2 : ℝ) * (N / ((Fintype.card S : ℝ) - M)) := fun u k =>
    add_nonneg (add_nonneg (add_nonneg (by positivity) (mul_nonneg (by positivity) ha0))
      (by positivity)) (mul_nonneg (by positivity) hb0)
  intro rem
  induction rem with
  | nil =>
    intro B t c _ _ hN ht hlen hB
    have hP : (P.card : ℝ) ≤ N := by
      have : P.card ≤ N := by simpa [openX] using hN
      exact_mod_cast this
    have h4 := H.a2_cnt_le shape hshape P M hM (B (view ([] : List (LeafSpec X M2)) ([] : List (D × R)))) Q2 q2 (hB (view ([] : List (LeafSpec X M2)) ([] : List (D × R)))).1 (hB (view ([] : List (LeafSpec X M2)) ([] : List (D × R)))).2 ⟨t, c⟩ ht
      (by simpa using hlen)
    simp only at h4
    have hopen : H.cnt (openX ([] : List (LeafSpec X M2))) t.usedIn = 0 := by simp [openX, cnt]
    simp only [layerIdeal, Strat.exp, hopen, add_zero, List.length_nil, Nat.cast_zero, zero_mul]
    calc (B (view ([] : List (LeafSpec X M2)) ([] : List (D × R)))).exp ⟨t, c⟩ (fun _ s' => min 1 ((H.cnt P s'.trace.usedIn : ℝ) / Fintype.card R))
        ≤ (B (view ([] : List (LeafSpec X M2)) ([] : List (D × R)))).exp ⟨t, c⟩
            (fun _ s' => (Fintype.card R : ℝ)⁻¹ * (H.cnt P s'.trace.usedIn : ℝ)) :=
          Strat.exp_mono (fun _ s' => (min_le_right _ _).trans (le_of_eq (by rw [div_eq_inv_mul]))) _ _
      _ = (Fintype.card R : ℝ)⁻¹ *
            (B (view ([] : List (LeafSpec X M2)) ([] : List (D × R)))).exp ⟨t, c⟩ (fun _ s' => (H.cnt P s'.trace.usedIn : ℝ)) :=
          Strat.exp_mul_left _ _ _ _
      _ ≤ (Fintype.card R : ℝ)⁻¹ * ((H.cnt P t.usedIn : ℝ) + q2 +
            (Q2 : ℝ) * ((Fintype.card R * P.card : ℕ) / ((Fintype.card S : ℝ) - M))) :=
          mul_le_mul_of_nonneg_left h4 (inv_nonneg.2 hR.le)
      _ = (H.cnt P t.usedIn : ℝ) / Fintype.card R + (q2 : ℝ) / Fintype.card R +
            (Q2 : ℝ) * (P.card / ((Fintype.card S : ℝ) - M)) := by
          push_cast
          field_simp
      _ ≤ _ := by
          have : (Q2 : ℝ) * (P.card / ((Fintype.card S : ℝ) - M)) ≤
              Q2 * (N / ((Fintype.card S : ℝ) - M)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hP hpos.le) (Nat.cast_nonneg _)
          linarith
  | cons l ls ih =>
    intro B t c hnd hP hN ht hlen hB
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hlx, hnd'⟩ := hnd
    have hP' : ∀ l' ∈ ls, l'.hidden = false → l'.x ∉ P :=
      fun l' h => hP l' (List.mem_cons_of_mem _ h)
    have hN' : P.card + (openX ls).card ≤ N :=
      le_trans (Nat.add_le_add_left (card_le_card (l34_openX_sub l ls)) _) hN
    rw [List.length_cons] at hlen
    have hlen' : t.length + 2 * ls.length + Q2 ≤ M := by omega
    have hO0 : l.x ∉ openX ls := l34_not_mem_openX ls l.x hlx
    have e : ((ls.length + 1 : ℕ) : ℝ) * (N * Kc / ((Fintype.card S : ℝ) - M)) =
        ls.length * (N * Kc / ((Fintype.card S : ℝ) - M)) + N * Kc / ((Fintype.card S : ℝ) - M) := by
      push_cast; ring
    rw [layerIdeal, Strat.exp_uniform, List.length_cons]
    simp only [Strat.exp_bind, Strat.exp, l34_view_cons]
    cases hh : l.hidden
    · -- an opened leaf
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [l34_openX_open l ls hh]
      have hlP : l.x ∉ P := hP l List.mem_cons_self hh
      refine (avg_le_of_le_ind_add _ _ (fun r => H.enc1 (r, l.x) ∈ t.usedIn)
        ((((H.cnt P t.usedIn + H.cnt (openX ls) t.usedIn : ℕ) : ℝ) / Fintype.card R +
          ((ls.length + 1 : ℕ) : ℝ) * (N * Kc / ((Fintype.card S : ℝ) - M)) +
          (q2 : ℝ) / Fintype.card R + (Q2 : ℝ) * (N / ((Fintype.card S : ℝ) - M))))
        (hnn _ _) fun r _ => ?_).trans ?_
      · by_cases hx1 : H.enc1 (r, l.x) ∈ t.usedIn
        · rw [ind_pos hx1]
          have h2 := hnn (H.cnt P t.usedIn + H.cnt (openX ls) t.usedIn) (ls.length + 1)
          refine le_trans ?_ (le_add_of_nonneg_right h2)
          apply Strat.exp_le zero_le_one
          intro d s1
          apply Strat.exp_le zero_le_one
          intro out s2
          apply Strat.exp_le zero_le_one
          intro _ _
          exact min_le_left _ _
        · rw [ind_neg hx1, zero_add]
          simp only [eval, Strat.exp]
          have hA : t.fwdAns (H.enc1 (r, l.x)) = t.freeOut := by simp [Trace.fwdAns, hx1]
          have hfree := (l34_card_free_ge t ht M hM (by omega)).2
          have hne : t.freeOut.Nonempty := by
            rw [← card_pos]
            have : (0 : ℝ) < t.freeOut.card := lt_of_lt_of_le hpos hfree
            exact_mod_cast this
          rw [hA]
          refine (avg_mono (h := fun o1 =>
            (((H.cnt P t.usedIn + H.cnt (openX ls) t.usedIn : ℕ) : ℝ) / Fintype.card R +
              (ls.length : ℝ) * (N * Kc / ((Fintype.card S : ℝ) - M)) +
              (q2 : ℝ) / Fintype.card R + (Q2 : ℝ) * (N / ((Fintype.card S : ℝ) - M))) +
            ((((univ ×ˢ P).filter fun p => H.enc1 p = H.enc2 (H.chop o1, l.m)).card +
              ((univ ×ˢ openX ls).filter fun p => H.enc1 p = H.enc2 (H.chop o1, l.m)).card : ℕ) : ℝ) /
              Fintype.card R) fun o1 ho1 => ?_).trans ?_
          · have hy1 : o1 ∈ t.fwdAns (H.enc1 (r, l.x)) := hA ▸ ho1
            have ht1 := ht.stepF hy1
            have hl1 := Trace.length_stepF_le t (H.enc1 (r, l.x)) o1
            refine avg_le (add_nonneg (hnn _ _) (by positivity)) fun o2 ho2 => ?_
            have ht2 := ht1.stepF ho2
            have hl2 := Trace.length_stepF_le (t.stepF (H.enc1 (r, l.x)) o1)
              (H.enc2 (H.chop o1, l.m)) o2
            refine (ih (fun v => B ((H.trunc o2, some r) :: v)) _ _ hnd' hP' hN' ht2 (by omega)
              (fun v => hB _)).trans ?_
            have c1 := H.l34_cnt_stepF_le P t (H.enc1 (r, l.x)) o1
            have c2 := H.l34_cnt_stepF_le P (t.stepF (H.enc1 (r, l.x)) o1)
              (H.enc2 (H.chop o1, l.m)) o2
            have c3 := H.l34_cnt_stepF_le (openX ls) t (H.enc1 (r, l.x)) o1
            have c4 := H.l34_cnt_stepF_le (openX ls) (t.stepF (H.enc1 (r, l.x)) o1)
              (H.enc2 (H.chop o1, l.m)) o2
            have z1 := H.l34_fib_enc1_eq_zero P r l.x hlP
            have z2 := H.l34_fib_enc1_eq_zero (openX ls) r l.x hO0
            have hc : ((H.cnt P ((t.stepF (H.enc1 (r, l.x)) o1).stepF (H.enc2 (H.chop o1, l.m)) o2).usedIn +
                H.cnt (openX ls) ((t.stepF (H.enc1 (r, l.x)) o1).stepF (H.enc2 (H.chop o1, l.m)) o2).usedIn : ℕ) : ℝ) ≤
                ((H.cnt P t.usedIn + H.cnt (openX ls) t.usedIn : ℕ) : ℝ) +
                ((((univ ×ˢ P).filter fun p => H.enc1 p = H.enc2 (H.chop o1, l.m)).card +
                  ((univ ×ˢ openX ls).filter fun p => H.enc1 p = H.enc2 (H.chop o1, l.m)).card : ℕ) : ℝ) := by
              rw [← Nat.cast_add]
              exact_mod_cast (by omega)
            have hd := div_le_div_of_nonneg_right hc hR.le
            rw [add_div] at hd
            linarith
          · rw [avg_add, avg_const hne]
            have hsum : ∑ o1 ∈ t.freeOut,
                ((((univ ×ˢ P).filter fun p => H.enc1 p = H.enc2 (H.chop o1, l.m)).card +
                  ((univ ×ˢ openX ls).filter fun p => H.enc1 p = H.enc2 (H.chop o1, l.m)).card : ℕ) : ℝ) /
                  Fintype.card R ≤ ((P.card + (openX ls).card : ℕ) : ℝ) * Kc := by
              rw [← sum_div, ← Nat.cast_sum, sum_add_distrib, div_le_iff₀ hR]
              have s1 := H.l34_sum_fib_enc2_le Kc hKc P l.m t.freeOut
              have s2 := H.l34_sum_fib_enc2_le Kc hKc (openX ls) l.m t.freeOut
              have : (∑ o1 ∈ t.freeOut, ((univ ×ˢ P).filter fun p => H.enc1 p = H.enc2 (H.chop o1, l.m)).card +
                  ∑ o1 ∈ t.freeOut, ((univ ×ˢ openX ls).filter fun p => H.enc1 p = H.enc2 (H.chop o1, l.m)).card) ≤
                  (P.card + (openX ls).card) * Kc * Fintype.card R := by
                calc _ ≤ Fintype.card R * P.card * Kc + Fintype.card R * (openX ls).card * Kc := by omega
                  _ = (P.card + (openX ls).card) * Kc * Fintype.card R := by ring
              exact_mod_cast this
            have havg := l34_avg_le_div _ _ _ _ (fun _ _ => by positivity) hsum hpos hfree
            have hNK : ((P.card + (openX ls).card : ℕ) : ℝ) * Kc / ((Fintype.card S : ℝ) - M) ≤
                N * Kc / ((Fintype.card S : ℝ) - M) := by
              refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)) hpos.le
              exact_mod_cast hN'
            rw [e]
            linarith
      · have havg := avg_ind_mem_le univ (univ.filter fun r : R => H.enc1 (r, l.x) ∈ t.usedIn)
          (fun r => H.enc1 (r, l.x) ∈ t.usedIn) (fun r _ h => mem_filter.2 ⟨mem_univ _, h⟩)
        rw [card_univ] at havg
        have hcnt := H.l34_cnt_open_cons (openX ls) l.x hO0 t.usedIn
        have hc : ((univ.filter fun r : R => H.enc1 (r, l.x) ∈ t.usedIn).card : ℝ) / Fintype.card R +
            ((H.cnt P t.usedIn + H.cnt (openX ls) t.usedIn : ℕ) : ℝ) / Fintype.card R ≤
            ((H.cnt P t.usedIn + H.cnt (insert l.x (openX ls)) t.usedIn : ℕ) : ℝ) / Fintype.card R := by
          rw [← add_div]
          refine div_le_div_of_nonneg_right ?_ hR.le
          exact_mod_cast (by omega)
        linarith
    · -- a hidden leaf
      simp only [↓reduceIte, Strat.exp_uniform, Strat.exp]
      rw [l34_openX_hidden l ls hh]
      refine avg_le (hnn _ _) fun r _ => avg_le (hnn _ _) fun d _ => ?_
      refine (ih (fun v => B ((d, none) :: v)) t c hnd' hP' hN' ht hlen' (fun v => hB _)).trans ?_
      rw [e]
      linarith


/-! ### Assembly -/

theorem ghostAvg_mono [Fintype R] [DecidableEq D] :
    ∀ (ls : List (LeafSpec X M2)) (out : List (D × R)) (φ ψ : List (Entry S) → ℝ),
      (∀ Γ, φ Γ ≤ ψ Γ) → H.ghostAvg ls out φ ≤ H.ghostAvg ls out ψ
  | [], _, φ, ψ, h => h []
  | _ :: _, [], φ, ψ, h => h []
  | l :: ls, p :: out, φ, ψ, h => by
    simp only [ghostAvg]
    split_ifs
    · exact avg_mono fun r _ => avg_mono fun o1 _ => avg_mono fun o2 _ =>
        ghostAvg_mono ls out _ _ fun Γ => h _
    · exact ghostAvg_mono ls out φ ψ h

theorem ghostAvg_add [Fintype R] [DecidableEq D] :
    ∀ (ls : List (LeafSpec X M2)) (out : List (D × R)) (φ ψ : List (Entry S) → ℝ),
      H.ghostAvg ls out (fun Γ => φ Γ + ψ Γ) = H.ghostAvg ls out φ + H.ghostAvg ls out ψ
  | [], _, φ, ψ => rfl
  | _ :: _, [], φ, ψ => rfl
  | l :: ls, p :: out, φ, ψ => by
    simp only [ghostAvg]
    split_ifs
    · simp only [ghostAvg_add ls out, avg_add]
    · exact ghostAvg_add ls out φ ψ

theorem ghostAvg_le_one [Fintype R] [DecidableEq D] :
    ∀ (ls : List (LeafSpec X M2)) (out : List (D × R)) (φ : List (Entry S) → ℝ),
      (∀ Γ, φ Γ ≤ 1) → H.ghostAvg ls out φ ≤ 1
  | [], _, φ, h => h []
  | _ :: _, [], φ, h => h []
  | l :: ls, p :: out, φ, h => by
    simp only [ghostAvg]
    split_ifs
    · exact avg_le zero_le_one fun r _ => avg_le zero_le_one fun o1 _ =>
        avg_le zero_le_one fun o2 _ => ghostAvg_le_one ls out _ fun Γ => h _
    · exact ghostAvg_le_one ls out φ h

theorem ghostAvg_const [Fintype R] [Nonempty R] [Fintype D] [DecidableEq D] (F : ℕ)
    (hF : ∀ d : D, (Finset.univ.filter fun s => H.trunc s = d).card = F) (a : ℝ) :
    ∀ (ls : List (LeafSpec X M2)) (out : List (D × R)), H.ghostAvg ls out (fun _ => a) = a
  | [], _ => rfl
  | _ :: _, [] => rfl
  | l :: ls, p :: out => by
    simp only [ghostAvg]
    split_ifs
    · haveI : Nonempty S := ⟨H.enc1 (Classical.arbitrary R, l.x)⟩
      have hS : (Fintype.card S : ℝ) = F * Fintype.card D := card_eq_of_regular H.trunc F hF
      have hF0 : (F : ℝ) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hS
        have : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
        linarith
      have hfib : (univ.filter fun o2 => H.trunc o2 = p.1).Nonempty := by
        rw [← Finset.card_pos, hF p.1]
        exact Nat.pos_of_ne_zero fun h0 => hF0 (by exact_mod_cast h0)
      simp only [ghostAvg_const F hF a ls out, avg_const hfib, avg_const univ_nonempty]
    · exact ghostAvg_const F hF a ls out

theorem eval_QB (r : R) (l : LeafSpec X M2) : (H.eval r l).QB 2 :=
  .fwd _ _ 1 fun _ => .fwd _ _ 0 fun _ => .done _ 0

theorem layerIdeal_QB [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] :
    ∀ ls : List (LeafSpec X M2), (H.layerIdeal ls).QB (2 * ls.length)
  | [] => .done _ _
  | l :: ls => by
    simp only [layerIdeal]
    refine Strat.QB_uniform fun r => ?_
    have h1 : (if l.hidden then Strat.uniform D fun d => Strat.done d else H.eval r l).QB 2 := by
      split_ifs
      · exact Strat.QB_uniform fun d => .done _ _
      · exact H.eval_QB r l
    have h2 := Strat.QB.bind h1 fun d =>
      Strat.QB.bind (layerIdeal_QB ls) fun out => Strat.QB.done ((d, r) :: out) 0
    refine h2.mono ?_
    simp only [List.length_cons]
    omega

theorem cnt_empty [Fintype R] [DecidableEq X] (P : Finset X) : H.cnt P ∅ = 0 := by
  simp [cnt]

theorem cnt_add_le [Fintype R] [DecidableEq X] (P O : Finset X) (hPO : Disjoint P O)
    (U : Finset S) : H.cnt P U + H.cnt O U ≤ U.card := by
  classical
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · refine Finset.card_le_card_of_injOn H.enc1 (fun p hp => ?_) H.enc1_inj.injOn
    rcases Finset.mem_union.1 hp with h | h <;> exact (Finset.mem_filter.1 h).2
  · rw [Finset.disjoint_left]
    intro p hp hp'
    have h1 := (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).2
    have h2 := (Finset.mem_product.1 (Finset.mem_filter.1 hp').1).2
    exact Finset.disjoint_left.1 hPO h1 h2

theorem hcount_le (ls : List (LeafSpec X M2)) : hcount ls ≤ ls.length :=
  List.length_filter_le _ _

theorem card_hidX_add_openX_le [DecidableEq X] (ls : List (LeafSpec X M2)) :
    (hidX ls).card + (openX ls).card ≤ ls.length := by
  unfold hidX openX
  refine (Nat.add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)).trans ?_
  simp only [List.length_map]
  induction ls with
  | nil => simp
  | cons l ls ih =>
    cases hl : l.hidden <;> simp [List.filter_cons, hl] <;> omega

theorem disjoint_hidX_openX [DecidableEq X] (ls : List (LeafSpec X M2))
    (hnd : (ls.map LeafSpec.x).Nodup) : Disjoint (hidX ls) (openX ls) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [hidX, openX, List.mem_toFinset, List.mem_map, List.mem_filter] at hx hx'
  obtain ⟨l, ⟨hl, hlh⟩, rfl⟩ := hx
  obtain ⟨l', ⟨hl', hlh'⟩, hx'⟩ := hx'
  have : l' = l := List.inj_on_of_nodup_map hnd hl' hl hx'
  subst this
  simp_all

theorem openX_not_mem_hidX [DecidableEq X] (ls : List (LeafSpec X M2))
    (hnd : (ls.map LeafSpec.x).Nodup) : ∀ l ∈ ls, l.hidden = false → l.x ∉ hidX ls := by
  intro l hl hlh hx
  refine Finset.disjoint_left.1 (disjoint_hidX_openX ls hnd) hx ?_
  simp only [openX, List.mem_toFinset, List.mem_map, List.mem_filter]
  exact ⟨l, ⟨hl, by simp [hlh]⟩, rfl⟩

theorem final_arith (a b Q n L h M s R D K F : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hQ : 0 ≤ Q)
    (hn : 0 ≤ n) (hL : 0 ≤ L) (hh : 0 ≤ h) (hM : M = a + Q + 2 * n) (hs : 0 < s) (hR : 0 < R)
    (hD : 1 ≤ D) (hK : 0 ≤ K) (hF : 0 < F) (hFD : F * D = s) (h2M : 2 * M ≤ s) (hLn : L ≤ n)
    (hhn : h ≤ n) :
    a / R + L * (n * K / (s - M)) + b / R + Q * (n / (s - M)) +
        h * (2 * n + M) * (1 / s + K / s + 1 / F) ≤
      2 * (a + b) / R + 8 * n * M * (K + D) / s := by
  have hM0 : 0 ≤ M := by rw [hM]; linarith
  have hsM : 0 < s - M := by linarith
  have t1 : n * K / (s - M) ≤ 2 * n * K / s := by
    rw [div_le_div_iff₀ hsM hs]
    have : 0 ≤ n * K := mul_nonneg hn hK
    nlinarith
  have t2 : n / (s - M) ≤ 2 * n / s := by
    rw [div_le_div_iff₀ hsM hs]
    nlinarith
  have t3 : 1 / F = D / s := by
    rw [div_eq_div_iff hF.ne' hs.ne', ← hFD]
    ring
  have e1 : L * (n * K / (s - M)) ≤ (2 * n * n * K) / s := by
    calc L * (n * K / (s - M)) ≤ n * (2 * n * K / s) :=
          mul_le_mul hLn t1 (div_nonneg (mul_nonneg hn hK) hsM.le) hn
      _ = (2 * n * n * K) / s := by ring
  have e2 : Q * (n / (s - M)) ≤ (2 * Q * n) / s := by
    calc Q * (n / (s - M)) ≤ Q * (2 * n / s) := mul_le_mul_of_nonneg_left t2 hQ
      _ = (2 * Q * n) / s := by ring
  have e3 : h * (2 * n + M) * (1 / s + K / s + 1 / F) ≤ (n * (2 * M) * (1 + K + D)) / s := by
    rw [t3]
    have hfac : 1 / s + K / s + D / s = (1 + K + D) / s := by ring
    rw [hfac]
    have h1 : h * (2 * n + M) ≤ n * (2 * M) := by
      apply mul_le_mul hhn (by linarith) (by linarith) hn
    calc h * (2 * n + M) * ((1 + K + D) / s) ≤ n * (2 * M) * ((1 + K + D) / s) :=
          mul_le_mul_of_nonneg_right h1 (div_nonneg (by linarith) hs.le)
      _ = (n * (2 * M) * (1 + K + D)) / s := by ring
  have e4 : (2 * n * n * K) / s + (2 * Q * n) / s + (n * (2 * M) * (1 + K + D)) / s ≤
      8 * n * M * (K + D) / s := by
    rw [← add_div, ← add_div]
    apply div_le_div_of_nonneg_right _ hs.le
    have hnM : 2 * n ≤ M := by rw [hM]; linarith
    have hQM : Q ≤ M := by rw [hM]; linarith
    have p1 : 2 * n * n * K ≤ n * M * K := by
      have := mul_le_mul_of_nonneg_right hnM (mul_nonneg hn hK)
      nlinarith
    have p2 : 2 * Q * n ≤ 2 * n * M * D := by
      have h1 : Q * n ≤ M * n := mul_le_mul_of_nonneg_right hQM hn
      have h2 : M * n ≤ M * n * D := le_mul_of_one_le_right (mul_nonneg hM0 hn) hD
      nlinarith
    have p3 : n * M ≤ n * M * D := le_mul_of_one_le_right (mul_nonneg hn hM0) hD
    have p4 : 0 ≤ n * M * K := mul_nonneg (mul_nonneg hn hM0) hK
    nlinarith
  have e5 : a / R + b / R ≤ 2 * (a + b) / R := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hR.le
  linarith

/-- The bound for one outcome of the first stage. -/
theorem core [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [DecidableEq D] [DecidableEq X]
    [DecidableEq C]
    (F Kc : ℕ) (hF : ∀ d : D, (Finset.univ.filter fun s => H.trunc s = d).card = F)
    (hKc : ∀ c : C, (Finset.univ.filter fun s => H.chop s = c).card ≤ Kc)
    (shape : S → Prop) (hshape : ∀ r x, shape (H.enc1 (r, x))) (n q1 q2 Q2 : ℕ)
    (ls : List (LeafSpec X M2)) (hls : ls.length ≤ n) (hnd : (ls.map LeafSpec.x).Nodup)
    (B : List (D × Option R) → Strat S Bool) (hB : ∀ v, (B v).QB Q2 ∧ (B v).FQB shape q2)
    (T : Trace S) (c : ℕ) (hT : T.WF) (hTl : T.length ≤ q1) :
    |((H.layerReal ls).bind fun out => B (view ls out)).exp ⟨T, c⟩ (fun b _ => ind (b = true)) -
        ((H.layerIdeal ls).bind fun out => B (view ls out)).exp ⟨T, c⟩
          (fun b _ => ind (b = true))| ≤
      2 * ((q1 + q2 : ℕ) : ℝ) / Fintype.card R +
        8 * (n : ℝ) * ((q1 + Q2 + 2 * n : ℕ) : ℝ) * (Kc + Fintype.card D) / Fintype.card S := by
  set f : Bool → ℝ := fun b => ind (b = true) with hf
  have hR0 : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hRHS0 : 0 ≤ 2 * ((q1 + q2 : ℕ) : ℝ) / Fintype.card R +
      8 * (n : ℝ) * ((q1 + Q2 + 2 * n : ℕ) : ℝ) * (Kc + Fintype.card D) / Fintype.card S := by
    positivity
  set Re := ((H.layerReal ls).bind fun out => B (view ls out)).exp ⟨T, c⟩ (fun b _ => f b)
    with hRe
  set Id := ((H.layerIdeal ls).bind fun out => B (view ls out)).exp ⟨T, c⟩ (fun b _ => f b)
    with hId
  have hRe01 : 0 ≤ Re ∧ Re ≤ 1 :=
    ⟨Strat.exp_nonneg (fun _ _ => ind_nonneg _) _ _, Strat.exp_le zero_le_one (fun _ _ => ind_le_one _) _ _⟩
  have hId01 : 0 ≤ Id ∧ Id ≤ 1 :=
    ⟨Strat.exp_nonneg (fun _ _ => ind_nonneg _) _ _, Strat.exp_le zero_le_one (fun _ _ => ind_le_one _) _ _⟩
  have hle1 : |Re - Id| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hRe01.1, hRe01.2, hId01.1, hId01.2]
  by_cases hnil : ls = []
  · subst hnil
    have : Re = Id := rfl
    rw [this, sub_self, abs_zero]
    exact hRHS0
  obtain ⟨l0, hl0⟩ := List.exists_mem_of_ne_nil ls hnil
  haveI : Nonempty S := ⟨H.enc1 (Classical.arbitrary R, l0.x)⟩
  have hS0 : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hn1 : 1 ≤ n := le_trans (List.length_pos_of_ne_nil hnil) hls
  have hD1 : (1 : ℝ) ≤ Fintype.card D := by exact_mod_cast Fintype.card_pos
  set M := q1 + Q2 + 2 * n with hMdef
  by_cases hbig : (Fintype.card S : ℝ) < 2 * (M : ℝ)
  · refine hle1.trans ?_
    have hK0 : (0 : ℝ) ≤ Kc := Nat.cast_nonneg _
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have h1 : (1 : ℝ) ≤ 8 * (n : ℝ) * (M : ℝ) * (Kc + Fintype.card D) / Fintype.card S := by
      rw [le_div_iff₀ hS0]
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
      have : (M : ℝ) ≤ (n : ℝ) * M * (Kc + Fintype.card D) := by
        have h2 : (1 : ℝ) ≤ (n : ℝ) * (Kc + Fintype.card D) := by nlinarith
        nlinarith
      nlinarith
    have h2 : 0 ≤ 2 * ((q1 + q2 : ℕ) : ℝ) / Fintype.card R := by positivity
    push_cast at h1 h2 ⊢
    linarith
  push_neg at hbig
  -- the coupling, both ways
  set P := hidX ls with hP
  set G := (H.layerIdeal ls).exp ⟨T, c⟩ (fun out s => (B (view ls out)).exp s fun b s' =>
    H.ghostAvg ls out fun Γ => ind (GhostBad Γ s'.trace)) with hG
  have one_sided : ∀ g : Bool → ℝ, (∀ b, 0 ≤ g b) → (∀ b, g b ≤ 1) →
      ((H.layerIdeal ls).bind fun out => B (view ls out)).exp ⟨T, c⟩ (fun b _ => g b) ≤
        ((H.layerReal ls).bind fun out => B (view ls out)).exp ⟨T, c⟩ (fun b _ => g b) + G := by
    intro g hg0 hg1
    rw [Strat.exp_bind, Strat.exp_bind]
    have hc := H.couple F hF g hg0 ls B [] T T c c (by simp) hT
    simp only [List.nil_append] at hc
    refine le_trans ?_ (add_le_add hc le_rfl)
    rw [hG, ← Strat.exp_add]
    refine Strat.exp_mono (fun out s => ?_) _ _
    rw [← Strat.exp_add]
    refine Strat.exp_mono (fun b s' => ?_) _ _
    rw [← H.ghostAvg_add]
    calc g b = H.ghostAvg ls out (fun _ => g b) := (H.ghostAvg_const F hF (g b) ls out).symm
      _ ≤ _ := H.ghostAvg_mono ls out _ _ fun Γ => by
        by_cases hb : GhostBad Γ s'.trace
        · rw [ind_pos hb, ind_neg (not_not.2 hb)]
          linarith [hg1 b]
        · rw [ind_neg hb, ind_pos hb]
          linarith
  have two : |Re - Id| ≤ G := by
    have h1 := one_sided f (fun _ => ind_nonneg _) (fun _ => ind_le_one _)
    have h2 := one_sided (fun b => 1 - f b) (fun b => by linarith [ind_le_one (b = true)])
      (fun b => by linarith [ind_nonneg (b = true)])
    rw [Strat.exp_one_sub (f := fun b _ => f b) _ _ hT,
      Strat.exp_one_sub (f := fun b _ => f b) _ _ hT] at h2
    rw [abs_le]
    constructor <;> linarith
  -- the bad event
  have hpostL : (H.layerIdeal ls).post ⟨T, c⟩ fun _ s1 =>
      s1.trace.WF ∧ s1.trace.length ≤ T.length + 2 * ls.length :=
    Strat.post_mono (fun _ _ hp => ⟨hp.1, hp.2.2⟩) (Strat.post_run (H.layerIdeal_QB ls) ⟨T, c⟩ hT)
  set E := (hcount ls : ℝ) * ((2 * n + M : ℕ) : ℝ) *
    (1 / (Fintype.card S : ℝ) + Kc / (Fintype.card S : ℝ) + 1 / (F : ℝ)) with hE
  have hE0 : 0 ≤ E := by positivity
  have hGle : G ≤ (H.layerIdeal ls).exp ⟨T, c⟩ (fun out s => (B (view ls out)).exp s fun b s' =>
      min 1 ((H.cnt P s'.trace.usedIn : ℝ) / Fintype.card R)) + E := by
    have step : G ≤ (H.layerIdeal ls).exp ⟨T, c⟩ (fun out s => (B (view ls out)).exp s fun b s' =>
        min 1 ((H.cnt P s'.trace.usedIn : ℝ) / Fintype.card R) + E) := by
      refine Strat.exp_le_exp_of_post hpostL fun out s1 hs1 => ?_
      refine Strat.exp_le_exp_of_post (Strat.post_run (hB (view ls out)).1 s1 hs1.1)
        fun b s' hs' => ?_
      have hlen' : s'.trace.length ≤ M := by
        have := hs'.2.2
        have := hs1.2
        omega
      have hU : s'.trace.usedIn.card ≤ M := by rw [hs'.1.card_usedIn]; exact hlen'
      have hV : s'.trace.usedOut.card ≤ M := by rw [hs'.1.card_usedOut]; exact hlen'
      have hL2 := H.ghost_bad_le F Kc hF hKc s'.trace M n hU hV ls out [] hnd
        (by simp [GhostBad, Strat.TouchedAny]) (by simp only [List.length_nil]; linarith [hcount_le ls])
      simp only [List.nil_append, List.map_nil, List.toFinset_nil, cnt_empty, add_zero] at hL2
      have hle1 := H.ghostAvg_le_one ls out (fun Γ => ind (GhostBad Γ s'.trace))
        (fun _ => ind_le_one _)
      rcases le_total ((H.cnt P s'.trace.usedIn : ℝ) / Fintype.card R) 1 with h | h
      · rw [min_eq_right h]
        linarith
      · rw [min_eq_left h]
        linarith
    refine step.trans (le_of_eq ?_)
    rw [Strat.exp_congr_of_post hpostL (g := fun out s => (B (view ls out)).exp s (fun b s' =>
      min 1 ((H.cnt P s'.trace.usedIn : ℝ) / Fintype.card R)) + E)]
    · rw [Strat.exp_add, Strat.exp_const E _ _ hT]
    · intro out s1 hs1
      rw [Strat.exp_add, Strat.exp_const E _ _ hs1.1]
  have hMn : 2 * n ≤ M := by omega
  have hMS : M < Fintype.card S := by
    have : 2 * M ≤ Fintype.card S := by exact_mod_cast hbig
    omega
  have hL3 := H.ideal_cnt_le Kc hKc shape hshape P n M Q2 q2 hMS ls B T c hnd
    (openX_not_mem_hidX ls hnd) (le_trans (card_hidX_add_openX_le ls) hls) hT (by omega) hB
  have hcntT : H.cnt P T.usedIn + H.cnt (openX ls) T.usedIn ≤ q1 :=
    (H.cnt_add_le P (openX ls) (disjoint_hidX_openX ls hnd) T.usedIn).trans
      (by rw [hT.card_usedIn]; exact hTl)
  have hcntT' : ((H.cnt P T.usedIn + H.cnt (openX ls) T.usedIn : ℕ) : ℝ) / Fintype.card R ≤
      (q1 : ℝ) / Fintype.card R :=
    div_le_div_of_nonneg_right (by exact_mod_cast hcntT) hR0.le
  have hSF : (Fintype.card S : ℝ) = F * Fintype.card D := card_eq_of_regular H.trunc F hF
  have hF0 : (0 : ℝ) < F := by
    rcases (Nat.cast_nonneg F : (0 : ℝ) ≤ F).eq_or_lt with h | h
    · rw [← h, zero_mul] at hSF
      linarith
    · exact h
  have hfin := final_arith (q1 : ℝ) q2 Q2 n ls.length (hcount ls) M (Fintype.card S)
    (Fintype.card R) (Fintype.card D) Kc F (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by rw [hMdef]; push_cast; ring) hS0 hR0 hD1 (Nat.cast_nonneg _) hF0 hSF.symm
    (by exact_mod_cast hbig) (by exact_mod_cast hls) (by exact_mod_cast (hcount_le ls).trans hls)
  have hEe : E = (hcount ls : ℝ) * (2 * n + M) *
      (1 / (Fintype.card S : ℝ) + Kc / (Fintype.card S : ℝ) + 1 / (F : ℝ)) := by
    rw [hE]
    push_cast
    ring
  push_cast at hfin ⊢
  rw [hEe] at hGle
  linarith

/-- **The layer bound.** `F` = states per digest (`trunc` regular), `Kc` = states per chaining value.
The first stage outputs at most `n` leaves with pairwise different `x` and a state. `shape` marks the states
that can be a leaf's first-call input; the second stage may make `Q2` queries in total but only `q2`
forward queries on shaped inputs. -/
theorem layer_bound [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [DecidableEq D] [DecidableEq X]
    [DecidableEq C]
    (F Kc : ℕ) (hF : ∀ d : D, (Finset.univ.filter fun s => H.trunc s = d).card = F)
    (hKc : ∀ c : C, (Finset.univ.filter fun s => H.chop s = c).card ≤ Kc)
    (shape : S → Prop) (hshape : ∀ r x, shape (H.enc1 (r, x)))
    {σ : Type} (A1 : Strat S (List (LeafSpec X M2) × σ)) (A2 : σ → List (D × Option R) → Strat S Bool)
    (n q1 q2 Q2 : ℕ) (hA1 : A1.QB q1)
    (hlist : A1.post PState.init fun a _ => a.1.length ≤ n ∧ (a.1.map LeafSpec.x).Nodup)
    (hA2 : ∀ st v, (A2 st v).QB Q2 ∧ (A2 st v).FQB shape q2) :
    |(A1.bind fun a => (H.layerReal a.1).bind fun out => A2 a.2 (view a.1 out)).prob PState.init
          (fun b _ => b = true) -
        (A1.bind fun a => (H.layerIdeal a.1).bind fun out => A2 a.2 (view a.1 out)).prob PState.init
          (fun b _ => b = true)| ≤
      2 * ((q1 + q2 : ℕ) : ℝ) / Fintype.card R +
        8 * (n : ℝ) * ((q1 + Q2 + 2 * n : ℕ) : ℝ) * (Kc + Fintype.card D) / Fintype.card S := by
  unfold Strat.prob
  rw [Strat.exp_bind, Strat.exp_bind]
  refine Strat.abs_exp_sub_le_of_post Trace.WF.nil
    (Strat.post_and (Strat.post_run hA1 PState.init Trace.WF.nil) hlist) ?_
  rintro ⟨ls, st⟩ ⟨T, c⟩ ⟨⟨hT, -, hlen⟩, hls, hnd⟩
  have hTl : T.length ≤ q1 := by simpa [PState.init] using hlen
  exact H.core F Kc hF hKc shape hshape n q1 q2 Q2 ls hls hnd (A2 st) (hA2 st) T c hT hTl

end SaltFirst

end CommitGolfCandidate.Permutation
