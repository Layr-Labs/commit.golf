import CommitGolfCandidate.S3PermTwoCall
import CommitGolfCandidate.S3PermGhost

/-!
# The two-call leaf hash: hiding with a fresh uniform salt

## The game that the bounds refer to

Everything runs against one lazily sampled permutation `π` of the state space `S`, starting from
the empty table. The adversary has two stages, both with forward and inverse access to `π` and
with private coins.

Real experiment, `TwoCall.hidingReal A1 A2`:

1. `A1` runs and outputs `(x1, m2, state)`: the first-call input (for the design, the tag and
   leaf bytes 0..176), the second message part (leaf bytes 176..256), and anything it wants to
   hand to the second stage. `A1` makes at most `q1` queries. It does not see the salt.
2. The game (not the adversary) draws the salt `r` uniformly from `R`, independently of
   everything so far. `r` is never given to the adversary.
3. The game computes the digest with two forward queries, which are added to the table and
   counted: `o1 = π (enc1 x1)`, `o2 = π (enc2 (r, chop o1, m2))`, `d = trunc o2`.
4. `A2 state d` runs, with the same permutation (so it can re-query anything, in either
   direction), and outputs a bit. `A2` makes at most `q2` queries.

Ideal experiment, `TwoCall.hidingIdeal A1 A2`: steps 1 and 4 are the same. In place of steps 2
and 3 the game makes only the first query `π (enc1 x1)` (its answer is discarded; it is kept so
that the table seen by `A2` contains the same salt-independent entry as in the real experiment)
and draws `d` uniformly from the digest space `D`. No salt exists and the second call is not
made.

So `q1` counts the queries before the digest is published and `q2` the queries after it; the
game's own two queries (one in the ideal experiment) are not part of `q1` or `q2`, and the
`+ 1` in the bound is the game's first query. The quantity bounded is
`|Pr[A2 outputs true in the real experiment] - Pr[A2 outputs true in the ideal experiment]|`.

`hiding_bound` (`hiding` is a Lean keyword): if every digest has exactly `K` preimages under
`trunc`, that difference is at most

  `(q1 + 1 + q2) / |R|  +  q2 · |D| / (|S| - (q1 + 1))  +  (q1 + 1) / |S|`.

The three terms: the second-call input `enc2 (r, chop o1, m2)` is already in the table when the
salt is drawn (at most `q1 + 1` of the `|R|` salts), or `A2` queries it or receives it as an
inverse answer (salt guessing, `q2 / |R|`); an inverse query or a fresh forward answer of `A2`
hits the hidden second-call output, of which only the digest part is known; the digest of a
fresh answer is not exactly uniform because used outputs are excluded.

`hiding_1600`: at `|S| = 2^1600`, `|R| = 2^128`, `|D| = 2^256` the difference is at most
`(q1 + 1 + q2) / 2^127`.

What this is not: it is a statement about one leaf. The opened leaves, the other unopened
leaves, the compression-function oracle and the Merkle tree are not in the game; a strategy can
simulate them (they are independent of `r`), but the reduction from the contract's hiding game
to this one, the hybrid over unopened leaves, and the removal of the discarded first query from
the ideal experiment are not done here (see PERMUTATION-PROOF.md, section 6).
-/

set_option linter.unusedSectionVars false

namespace CommitGolfCandidate.Permutation

open Finset

variable {S : Type} [Fintype S] [DecidableEq S]

/-! ### Counting new table entries -/

theorem usedIn_subset_of_suffix {T T' : Trace S} (h : T <:+ T') : T.usedIn ⊆ T'.usedIn :=
  fun x hx => by
    obtain ⟨e, he, rfl⟩ := Trace.mem_usedIn.1 hx
    exact Trace.mem_usedIn.2 ⟨e, h.subset he, rfl⟩

theorem usedOut_subset_of_suffix {T T' : Trace S} (h : T <:+ T') : T.usedOut ⊆ T'.usedOut :=
  fun x hx => by
    obtain ⟨e, he, rfl⟩ := Trace.mem_usedOut.1 hx
    exact Trace.mem_usedOut.2 ⟨e, h.subset he, rfl⟩

theorem card_new_in_le {T T' : Trace S} (hT : T.WF) (hT' : T'.WF) (hsuf : T <:+ T') (q : ℕ)
    (hlen : T'.length ≤ T.length + q) : (T'.usedIn \ T.usedIn).card ≤ q := by
  have := Finset.card_sdiff_add_card_eq_card (usedIn_subset_of_suffix hsuf)
  rw [hT.card_usedIn, hT'.card_usedIn] at this
  omega

theorem card_new_out_le {T T' : Trace S} (hT : T.WF) (hT' : T'.WF) (hsuf : T <:+ T') (q : ℕ)
    (hlen : T'.length ≤ T.length + q) : (T'.usedOut \ T.usedOut).card ≤ q := by
  have := Finset.card_sdiff_add_card_eq_card (usedOut_subset_of_suffix hsuf)
  rw [hT.card_usedOut, hT'.card_usedOut] at this
  omega

/-- If an injective map sends every `i` with `p i` into a set of at most `n` elements, the
indicators sum to at most `n`. -/
theorem sum_ind_le_of_injective {ι κ : Type} (A : Finset ι) (F : Finset κ) (p : ι → Prop)
    (w : ι → κ) (hw : Function.Injective w) (h : ∀ i ∈ A, p i → w i ∈ F) :
    ∑ i ∈ A, ind (p i) ≤ (F.card : ℝ) := by
  classical
  rw [sum_ind]
  exact_mod_cast Finset.card_le_card_of_injOn w
    (fun i hi => h i (Finset.mem_filter.1 hi).1 (Finset.mem_filter.1 hi).2) hw.injOn

/-- Of the points `W r` of an injective family, at most `q` become used inputs when the table
grows by at most `q` entries. -/
theorem sum_ind_new_in {R : Type} [Fintype R] (W : R → S) (hW : Function.Injective W)
    {T T' : Trace S} (hT : T.WF) (hT' : T'.WF) (hsuf : T <:+ T') (q : ℕ)
    (hlen : T'.length ≤ T.length + q) :
    ∑ r : R, ind (W r ∈ T'.usedIn ∧ W r ∉ T.usedIn) ≤ (q : ℝ) := by
  refine (sum_ind_le_of_injective univ (T'.usedIn \ T.usedIn) _ W hW
    fun r _ h => Finset.mem_sdiff.2 h).trans ?_
  exact_mod_cast card_new_in_le hT hT' hsuf q hlen

theorem sum_ind_new_out (G : Finset S) {T T' : Trace S} (hT : T.WF) (hT' : T'.WF)
    (hsuf : T <:+ T') (hG : G ⊆ T.freeOut) (q : ℕ) (hlen : T'.length ≤ T.length + q) :
    ∑ o ∈ G, ind (o ∈ T'.usedOut) ≤ (q : ℝ) := by
  refine (sum_ind_le G (T'.usedOut \ T.usedOut) _ fun o ho h =>
    Finset.mem_sdiff.2 ⟨h, Trace.mem_freeOut.1 (hG ho)⟩).trans ?_
  exact_mod_cast card_new_out_le hT hT' hsuf q hlen

theorem sum_ind_used_in {R : Type} [Fintype R] (W : R → S) (hW : Function.Injective W)
    {T : Trace S} (hT : T.WF) : ∑ r : R, ind (W r ∈ T.usedIn) ≤ (T.length : ℝ) := by
  refine (sum_ind_le_of_injective univ T.usedIn _ W hW fun r _ h => h).trans ?_
  rw [hT.card_usedIn]

/-! ### Regular truncations -/

theorem sum_comp_of_regular {D : Type} [Fintype D] [DecidableEq D] (tr : S → D) (K : ℕ)
    (hK : ∀ d : D, (univ.filter fun s => tr s = d).card = K) (h : D → ℝ) :
    ∑ o : S, h (tr o) = (K : ℝ) * ∑ d, h d := by
  rw [← Finset.sum_fiberwise univ tr fun o => h (tr o), Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hc : ∀ o ∈ univ.filter (fun s => tr s = d), h (tr o) = h d := fun o ho => by
    rw [(Finset.mem_filter.1 ho).2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, hK, nsmul_eq_mul]

theorem card_eq_of_regular {D : Type} [Fintype D] [DecidableEq D] (tr : S → D) (K : ℕ)
    (hK : ∀ d : D, (univ.filter fun s => tr s = d).card = K) :
    (Fintype.card S : ℝ) = (K : ℝ) * Fintype.card D := by
  have h := sum_comp_of_regular tr K hK fun _ => 1
  simpa using h

/-- The digest of a uniform unused output is close to uniform: for a `[0, 1]`-valued `h`, the
average of `h ∘ tr` over the unused outputs is within `|T| / |S|` of the average of `h`. -/
theorem abs_avg_free_sub_avg_univ {D : Type} [Fintype D] [DecidableEq D] (tr : S → D) (K : ℕ)
    (hK : ∀ d : D, (univ.filter fun s => tr s = d).card = K) (T : Trace S) (hwf : T.WF)
    (hlt : T.length < Fintype.card S) (h : D → ℝ) (h0 : ∀ d, 0 ≤ h d) (h1 : ∀ d, h d ≤ 1) :
    |avg T.freeOut (fun o => h (tr o)) - avg univ h| ≤ (T.length : ℝ) / Fintype.card S := by
  have hi0 : (0 : ℝ) ≤ T.length := Nat.cast_nonneg _
  have hiN : (T.length : ℝ) < Fintype.card S := by exact_mod_cast hlt
  have hF : (T.freeOut.card : ℝ) = (Fintype.card S : ℝ) - T.length := by
    rw [hwf.card_freeOut, Nat.cast_sub hlt.le]
  have hFpos : (0 : ℝ) < T.freeOut.card := by rw [hF]; linarith
  have hN : (0 : ℝ) < Fintype.card S := by linarith
  have hNK := card_eq_of_regular tr K hK
  have hK0 : (K : ℝ) ≠ 0 := by
    intro hk
    rw [hk, zero_mul] at hNK
    linarith
  -- the three sums
  have hsplit : ∑ o ∈ T.usedOut, h (tr o) + ∑ o ∈ T.freeOut, h (tr o) = ∑ o : S, h (tr o) :=
    Finset.sum_add_sum_compl T.usedOut _
  have hUs0 : 0 ≤ ∑ o ∈ T.usedOut, h (tr o) := Finset.sum_nonneg fun o _ => h0 _
  have hUs1 : ∑ o ∈ T.usedOut, h (tr o) ≤ T.length := by
    have : ∑ o ∈ T.usedOut, h (tr o) ≤ ∑ _o ∈ T.usedOut, (1 : ℝ) :=
      Finset.sum_le_sum fun o _ => h1 _
    rw [Finset.sum_const, hwf.card_usedOut, nsmul_eq_mul, mul_one] at this
    exact this
  have hm0 : 0 ≤ avg T.freeOut (fun o => h (tr o)) := avg_nonneg fun o _ => h0 _
  have hm1 : avg T.freeOut (fun o => h (tr o)) ≤ 1 := avg_le zero_le_one fun o _ => h1 _
  have hFs : ∑ o ∈ T.freeOut, h (tr o) =
      avg T.freeOut (fun o => h (tr o)) * T.freeOut.card := by
    unfold avg
    rw [div_mul_cancel₀ _ hFpos.ne']
  have hideal : avg univ h = (∑ o : S, h (tr o)) / Fintype.card S := by
    unfold avg
    rw [sum_comp_of_regular tr K hK h, hNK, Finset.card_univ, mul_div_mul_left _ _ hK0]
  rw [hideal, ← hsplit, hFs, hF]
  generalize avg T.freeOut (fun o => h (tr o)) = m at hm0 hm1 ⊢
  generalize ∑ o ∈ T.usedOut, h (tr o) = u at hUs0 hUs1 ⊢
  generalize (T.length : ℝ) = i at hi0 hiN hUs1 ⊢
  generalize (Fintype.card S : ℝ) = N at hiN hN ⊢
  have hN' : N ≠ 0 := hN.ne'
  have e : m - (u + m * (N - i)) / N = (m * i - u) / N := by
    rw [eq_div_iff hN', sub_mul, div_mul_cancel₀ _ hN']
    ring
  rw [e, abs_div, abs_of_pos hN]
  refine div_le_div_of_nonneg_right ?_ hN.le
  have hmi0 : 0 ≤ m * i := mul_nonneg hm0 hi0
  have hmi1 : m * i ≤ i := mul_le_of_le_one_left hi0 hm1
  rw [abs_le]
  constructor <;> linarith

namespace Strat

variable {α : Type}

/-- The probability that a bit-valued strategy outputs `true`. -/
noncomputable def acc (A : Strat S Bool) (s : PState S) : ℝ := A.exp s fun b _ => ind (b = true)

theorem acc_nonneg (A : Strat S Bool) (s : PState S) : 0 ≤ acc A s :=
  exp_nonneg (fun _ _ => ind_nonneg _) _ _

theorem acc_le_one (A : Strat S Bool) (s : PState S) : acc A s ≤ 1 :=
  exp_le zero_le_one (fun _ _ => ind_le_one _) _ _

theorem acc_eq_prob (A : Strat S Bool) (s : PState S) :
    acc A s = A.prob s fun b _ => b = true := rfl

/-- The probability that the run makes `x`, unused at the start, a used input. -/
noncomputable def touchIn (A : Strat S α) (s : PState S) (x : S) : ℝ :=
  A.exp s fun _ s' => ind (x ∈ s'.trace.usedIn ∧ x ∉ s.trace.usedIn)

/-- The probability that the run ends with `o` among the used outputs. -/
noncomputable def touchOut (A : Strat S α) (s : PState S) (o : S) : ℝ :=
  A.exp s fun _ s' => ind (o ∈ s'.trace.usedOut)

theorem touchIn_nonneg (A : Strat S α) (s : PState S) (x : S) : 0 ≤ touchIn A s x :=
  exp_nonneg (fun _ _ => ind_nonneg _) _ _

theorem touchOut_nonneg (A : Strat S α) (s : PState S) (o : S) : 0 ≤ touchOut A s o :=
  exp_nonneg (fun _ _ => ind_nonneg _) _ _

/-- What every run of a `q`-query strategy from a well-formed state preserves. -/
theorem post_run {A : Strat S α} {q : ℕ} (hA : A.QB q) (s : PState S) (hs : s.trace.WF) :
    A.post s fun _ s' =>
      s'.trace.WF ∧ s.trace <:+ s'.trace ∧ s'.trace.length ≤ s.trace.length + q :=
  post_mono (fun _ _ hp => ⟨hp.1.1, hp.1.2.1, hp.2.1⟩)
    (post_and (post_inv A s hs) (post_QB hA s))

theorem sum_touchIn_le {R : Type} [Fintype R] (W : R → S) (hW : Function.Injective W)
    {A : Strat S α} {q : ℕ} (hA : A.QB q) (s : PState S) (hs : s.trace.WF) :
    ∑ r : R, touchIn A s (W r) ≤ (q : ℝ) := by
  unfold touchIn
  rw [← exp_sum]
  exact exp_le_of_post hs (post_run hA s hs) fun _ s' hp =>
    sum_ind_new_in W hW hs hp.1 hp.2.1 q hp.2.2

theorem sum_touchOut_le (G : Finset S) {A : Strat S α} {q : ℕ} (hA : A.QB q) (s : PState S)
    (hs : s.trace.WF) (hG : G ⊆ s.trace.freeOut) : ∑ o ∈ G, touchOut A s o ≤ (q : ℝ) := by
  unfold touchOut
  rw [← exp_sum]
  exact exp_le_of_post hs (post_run hA s hs) fun _ s' hp =>
    sum_ind_new_out G hs hp.1 hp.2.1 hG q hp.2.2

/-- The ghost lemma for acceptance probabilities, with the touch event split into its input and
output halves. -/
theorem abs_acc_ghost_le (A : Strat S Bool) (T : Trace S) (c c' : ℕ) (hwf : T.WF) (x o : S)
    (hx : x ∉ T.usedIn) (ho : o ∉ T.usedOut) :
    |acc A ⟨⟨.fwd, x, o⟩ :: T, c'⟩ - acc A ⟨T, c⟩| ≤
      touchIn A ⟨T, c⟩ x + touchOut A ⟨T, c⟩ o := by
  have hg := abs_exp_ghost_le ⟨.fwd, x, o⟩ (fun b : Bool => ind (b = true))
    (fun _ => ind_nonneg _) (fun _ => ind_le_one _) A T (⟨.fwd, x, o⟩ :: T) c c'
    (List.Perm.refl _) (hwf.cons hx ho)
  refine hg.trans ?_
  show A.exp ⟨T, c⟩ (fun _ s' => ind (Touched ⟨.fwd, x, o⟩ s'.trace)) ≤
    A.exp ⟨T, c⟩ (fun _ s' => ind (x ∈ s'.trace.usedIn ∧ x ∉ T.usedIn)) +
      A.exp ⟨T, c⟩ (fun _ s' => ind (o ∈ s'.trace.usedOut))
  rw [← exp_add]
  refine exp_mono (fun _ s' => ?_) _ _
  by_cases hT : Touched ⟨.fwd, x, o⟩ s'.trace
  · rw [ind_pos hT]
    rcases hT with hT | hT
    · rw [ind_pos (⟨hT, hx⟩ : x ∈ s'.trace.usedIn ∧ x ∉ T.usedIn)]
      linarith [ind_nonneg (o ∈ s'.trace.usedOut)]
    · rw [ind_pos (hT : o ∈ s'.trace.usedOut)]
      linarith [ind_nonneg (x ∈ s'.trace.usedIn ∧ x ∉ T.usedIn)]
  · rw [ind_neg hT]
    exact add_nonneg (ind_nonneg _) (ind_nonneg _)

end Strat

namespace TwoCall

open Strat

variable {X1 R C M2 D : Type} (H : TwoCall S X1 R C M2 D)

/-- The second call with a uniform salt against a uniform digest, from a fixed state: the core
of the hiding proof. `c0` is the chaining value produced by the first call. -/
theorem hiding_core [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [DecidableEq D]
    (K : ℕ) (hK : ∀ d : D, (univ.filter fun s => H.trunc s = d).card = K)
    (c0 : C) (m2 : M2) (A2 : D → Strat S Bool) (q2 : ℕ) (hA2 : ∀ d, (A2 d).QB q2)
    (T : Trace S) (c : ℕ) (hwf : T.WF) (hlt : T.length < Fintype.card S) :
    |avg univ (fun r : R =>
          acc (Strat.fwd (H.enc2 (r, c0, m2)) fun o2 => A2 (H.trunc o2)) ⟨T, c⟩) -
        avg univ (fun d : D => acc (A2 d) ⟨T, c⟩)| ≤
      ((T.length : ℝ) + q2) / Fintype.card R +
        (q2 : ℝ) * Fintype.card D / ((Fintype.card S : ℝ) - T.length) +
        (T.length : ℝ) / Fintype.card S := by
  have hW : Function.Injective fun r : R => H.enc2 (r, c0, m2) := fun r r' h => by
    have := H.enc2_inj h
    simp only [Prod.mk.injEq] at this
    exact this.1
  have hF : (T.freeOut.card : ℝ) = (Fintype.card S : ℝ) - T.length := by
    rw [hwf.card_freeOut, Nat.cast_sub hlt.le]
  have hFpos : (0 : ℝ) < T.freeOut.card := by
    rw [hF]
    have : (T.length : ℝ) < Fintype.card S := by exact_mod_cast hlt
    linarith
  have hRpos : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  -- the middle point: the digest of a uniform unused output is handed to `A2`
  set M : ℝ := avg T.freeOut (fun o => acc (A2 (H.trunc o)) ⟨T, c⟩) with hM
  have hM0 : 0 ≤ M := avg_nonneg fun o _ => acc_nonneg _ _
  have hM1 : M ≤ 1 := avg_le zero_le_one fun o _ => acc_le_one _ _
  -- Step A: one salt
  have stepA : ∀ r : R,
      |acc (Strat.fwd (H.enc2 (r, c0, m2)) fun o2 => A2 (H.trunc o2)) ⟨T, c⟩ - M| ≤
        ind (H.enc2 (r, c0, m2) ∈ T.usedIn) +
          avg T.freeOut (fun o =>
            touchIn (A2 (H.trunc o)) ⟨T, c⟩ (H.enc2 (r, c0, m2)) +
              touchOut (A2 (H.trunc o)) ⟨T, c⟩ o) := by
    intro r
    have hnn : 0 ≤ avg T.freeOut (fun o =>
        touchIn (A2 (H.trunc o)) ⟨T, c⟩ (H.enc2 (r, c0, m2)) +
          touchOut (A2 (H.trunc o)) ⟨T, c⟩ o) :=
      avg_nonneg fun o _ => add_nonneg (touchIn_nonneg _ _ _) (touchOut_nonneg _ _ _)
    by_cases hr : H.enc2 (r, c0, m2) ∈ T.usedIn
    · rw [ind_pos hr]
      have t0 := acc_nonneg (Strat.fwd (H.enc2 (r, c0, m2)) fun o2 => A2 (H.trunc o2)) ⟨T, c⟩
      have t1 := acc_le_one (Strat.fwd (H.enc2 (r, c0, m2)) fun o2 => A2 (H.trunc o2)) ⟨T, c⟩
      rw [abs_le]
      constructor <;> linarith
    · rw [ind_neg hr, zero_add]
      have e1 : T.fwdAns (H.enc2 (r, c0, m2)) = T.freeOut := if_neg hr
      have e3 : ∀ o, T.stepF (H.enc2 (r, c0, m2)) o = ⟨.fwd, H.enc2 (r, c0, m2), o⟩ :: T :=
        fun o => if_neg hr
      have hexp : acc (Strat.fwd (H.enc2 (r, c0, m2)) fun o2 => A2 (H.trunc o2)) ⟨T, c⟩ =
          avg T.freeOut (fun o =>
            acc (A2 (H.trunc o)) ⟨⟨.fwd, H.enc2 (r, c0, m2), o⟩ :: T, c + 1⟩) := by
        simp only [acc, Strat.exp, e1, e3]
      rw [hexp, hM]
      exact (abs_avg_sub_le _ _ _).trans (avg_mono fun o ho =>
        abs_acc_ghost_le (A2 (H.trunc o)) T c (c + 1) hwf _ o hr (Trace.mem_freeOut.1 ho))
  -- Step B: average over the salt
  have stepB : |avg univ (fun r : R =>
        acc (Strat.fwd (H.enc2 (r, c0, m2)) fun o2 => A2 (H.trunc o2)) ⟨T, c⟩) - M| ≤
      ((T.length : ℝ) + q2) / Fintype.card R +
        (q2 : ℝ) * Fintype.card D / ((Fintype.card S : ℝ) - T.length) := by
    have h1 : |avg univ (fun r : R =>
          acc (Strat.fwd (H.enc2 (r, c0, m2)) fun o2 => A2 (H.trunc o2)) ⟨T, c⟩) - M| ≤
        avg univ (fun r : R => ind (H.enc2 (r, c0, m2) ∈ T.usedIn) +
          avg T.freeOut (fun o =>
            touchIn (A2 (H.trunc o)) ⟨T, c⟩ (H.enc2 (r, c0, m2)) +
              touchOut (A2 (H.trunc o)) ⟨T, c⟩ o)) := by
      have hc : M = avg univ (fun _ : R => M) := (avg_const Finset.univ_nonempty M).symm
      calc _ = |avg univ (fun r : R =>
              acc (Strat.fwd (H.enc2 (r, c0, m2)) fun o2 => A2 (H.trunc o2)) ⟨T, c⟩) -
            avg univ (fun _ : R => M)| := by rw [← hc]
        _ ≤ _ := (abs_avg_sub_le _ _ _).trans (avg_mono fun r _ => stepA r)
    refine h1.trans ?_
    rw [avg_add]
    -- the salts whose second-call input is already in the table
    have b1 : avg univ (fun r : R => ind (H.enc2 (r, c0, m2) ∈ T.usedIn)) ≤
        (T.length : ℝ) / Fintype.card R := by
      unfold avg
      rw [Finset.card_univ]
      exact div_le_div_of_nonneg_right (sum_ind_used_in _ hW hwf) (Nat.cast_nonneg _)
    -- touching the second-call input later
    have b2 : avg univ (fun r : R => avg T.freeOut (fun o =>
        touchIn (A2 (H.trunc o)) ⟨T, c⟩ (H.enc2 (r, c0, m2)))) ≤
        (q2 : ℝ) / Fintype.card R := by
      rw [avg_comm]
      refine avg_le (by positivity) fun o _ => ?_
      unfold avg
      rw [Finset.card_univ]
      exact div_le_div_of_nonneg_right
        (sum_touchIn_le (fun r : R => H.enc2 (r, c0, m2)) hW (hA2 _) ⟨T, c⟩ hwf)
        (Nat.cast_nonneg _)
    -- touching the hidden second-call output
    have b3 : avg T.freeOut (fun o => touchOut (A2 (H.trunc o)) ⟨T, c⟩ o) ≤
        (q2 : ℝ) * Fintype.card D / ((Fintype.card S : ℝ) - T.length) := by
      unfold avg
      rw [hF]
      refine div_le_div_of_nonneg_right ?_ (by rw [← hF]; exact hFpos.le)
      rw [← Finset.sum_fiberwise T.freeOut H.trunc]
      have hfib : ∀ d ∈ (univ : Finset D),
          ∑ o ∈ T.freeOut.filter (fun o => H.trunc o = d),
            touchOut (A2 (H.trunc o)) ⟨T, c⟩ o ≤ (q2 : ℝ) := by
        intro d _
        have hc : ∀ o ∈ T.freeOut.filter (fun o => H.trunc o = d),
            touchOut (A2 (H.trunc o)) ⟨T, c⟩ o = touchOut (A2 d) ⟨T, c⟩ o := fun o ho => by
          rw [(Finset.mem_filter.1 ho).2]
        rw [Finset.sum_congr rfl hc]
        exact sum_touchOut_le _ (hA2 d) ⟨T, c⟩ hwf (Finset.filter_subset _ _)
      refine (Finset.sum_le_sum hfib).trans_eq ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
    have hsplit : avg univ (fun r : R => avg T.freeOut (fun o =>
          touchIn (A2 (H.trunc o)) ⟨T, c⟩ (H.enc2 (r, c0, m2)) +
            touchOut (A2 (H.trunc o)) ⟨T, c⟩ o)) =
        avg univ (fun r : R => avg T.freeOut (fun o =>
          touchIn (A2 (H.trunc o)) ⟨T, c⟩ (H.enc2 (r, c0, m2)))) +
        avg T.freeOut (fun o => touchOut (A2 (H.trunc o)) ⟨T, c⟩ o) := by
      have : ∀ r : R, avg T.freeOut (fun o =>
          touchIn (A2 (H.trunc o)) ⟨T, c⟩ (H.enc2 (r, c0, m2)) +
            touchOut (A2 (H.trunc o)) ⟨T, c⟩ o) =
          avg T.freeOut (fun o => touchIn (A2 (H.trunc o)) ⟨T, c⟩ (H.enc2 (r, c0, m2))) +
            avg T.freeOut (fun o => touchOut (A2 (H.trunc o)) ⟨T, c⟩ o) := fun r => avg_add
      rw [avg_congr fun r _ => this r, avg_add, avg_const Finset.univ_nonempty]
    rw [hsplit, add_div]
    linarith
  -- Step C: the digest of a uniform unused output against a uniform digest
  have stepC : |M - avg univ (fun d : D => acc (A2 d) ⟨T, c⟩)| ≤
      (T.length : ℝ) / Fintype.card S :=
    abs_avg_free_sub_avg_univ H.trunc K hK T hwf hlt (fun d => acc (A2 d) ⟨T, c⟩)
      (fun d => acc_nonneg _ _) (fun d => acc_le_one _ _)
  calc _ ≤ |avg univ (fun r : R =>
            acc (Strat.fwd (H.enc2 (r, c0, m2)) fun o2 => A2 (H.trunc o2)) ⟨T, c⟩) - M| +
          |M - avg univ (fun d : D => acc (A2 d) ⟨T, c⟩)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add stepB stepC

/-- The real hiding experiment: the digest of the leaf chosen by `A1`, salted with a fresh
uniform `r`, is given to `A2`. -/
noncomputable def hidingReal [Fintype R] [Nonempty R] {σ : Type}
    (A1 : Strat S (X1 × M2 × σ)) (A2 : σ → D → Strat S Bool) : Strat S Bool :=
  A1.bind fun a => Strat.uniform R fun r => (H.eval (a.1, r, a.2.1)).bind (A2 a.2.2)

/-- The ideal hiding experiment: the first (salt-independent) call is made, and `A2` is given a
uniform digest. -/
noncomputable def hidingIdeal [Fintype D] [Nonempty D] {σ : Type}
    (A1 : Strat S (X1 × M2 × σ)) (A2 : σ → D → Strat S Bool) : Strat S Bool :=
  A1.bind fun a => Strat.fwd (H.enc1 a.1) fun _ => Strat.uniform D fun d => A2 a.2.2 d

/-- **Hiding of the two-call leaf hash.** With a fresh uniform salt the digest is statistically
close to uniform given all queries of both adversary stages: the acceptance probabilities of the
real and the ideal experiment differ by at most

  `(q1 + 1 + q2) / |R| + q2 · |D| / (|S| - (q1 + 1)) + (q1 + 1) / |S|`. -/
theorem hiding_bound [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [DecidableEq D]
    (K : ℕ) (hK : ∀ d : D, (univ.filter fun s => H.trunc s = d).card = K)
    {σ : Type} (A1 : Strat S (X1 × M2 × σ)) (A2 : σ → D → Strat S Bool) (q1 q2 : ℕ)
    (hA1 : A1.QB q1) (hA2 : ∀ st d, (A2 st d).QB q2) (hq : q1 + 1 < Fintype.card S) :
    |(H.hidingReal A1 A2).prob PState.init (fun b _ => b = true) -
        (H.hidingIdeal A1 A2).prob PState.init (fun b _ => b = true)| ≤
      ((q1 : ℝ) + 1 + q2) / Fintype.card R +
        (q2 : ℝ) * Fintype.card D / ((Fintype.card S : ℝ) - ((q1 : ℝ) + 1)) +
        ((q1 : ℝ) + 1) / Fintype.card S := by
  have hpos : (0 : ℝ) < (Fintype.card S : ℝ) - ((q1 : ℝ) + 1) := by
    have : ((q1 + 1 : ℕ) : ℝ) < Fintype.card S := by exact_mod_cast hq
    push_cast at this
    linarith
  have hε0 : 0 ≤ ((q1 : ℝ) + 1 + q2) / Fintype.card R +
      (q2 : ℝ) * Fintype.card D / ((Fintype.card S : ℝ) - ((q1 : ℝ) + 1)) +
      ((q1 : ℝ) + 1) / Fintype.card S :=
    add_nonneg (add_nonneg (div_nonneg (by positivity) (Nat.cast_nonneg _))
      (div_nonneg (by positivity) hpos.le)) (div_nonneg (by positivity) (Nat.cast_nonneg _))
  have hR : (H.hidingReal A1 A2).prob PState.init (fun b _ => b = true) =
      A1.exp PState.init (fun a s1 =>
        acc (Strat.uniform R fun r => (H.eval (a.1, r, a.2.1)).bind (A2 a.2.2)) s1) :=
    Strat.exp_bind _ _ _ _
  have hI : (H.hidingIdeal A1 A2).prob PState.init (fun b _ => b = true) =
      A1.exp PState.init (fun a s1 =>
        acc (Strat.fwd (H.enc1 a.1) fun _ => Strat.uniform D fun d => A2 a.2.2 d) s1) :=
    Strat.exp_bind _ _ _ _
  rw [hR, hI]
  refine abs_exp_sub_le_of_post Trace.WF.nil (post_run hA1 PState.init Trace.WF.nil) ?_
  rintro ⟨x1, m2, st⟩ s1 ⟨hwf1, -, hlen1⟩
  have hlen1' : s1.trace.length ≤ q1 := by simpa [PState.init] using hlen1
  have hreal : acc (Strat.uniform R fun r => (H.eval (x1, r, m2)).bind (A2 st)) s1 =
      avg (s1.trace.fwdAns (H.enc1 x1)) (fun o1 => avg univ (fun r : R =>
        acc (Strat.fwd (H.enc2 (r, H.chop o1, m2)) fun o2 => A2 st (H.trunc o2))
          ⟨s1.trace.stepF (H.enc1 x1) o1, s1.count + 1⟩)) := by
    unfold acc
    rw [exp_uniform, avg_comm]
    rfl
  have hideal : acc (Strat.fwd (H.enc1 x1) fun _ => Strat.uniform D fun d => A2 st d) s1 =
      avg (s1.trace.fwdAns (H.enc1 x1)) (fun o1 => avg univ (fun d : D =>
        acc (A2 st d) ⟨s1.trace.stepF (H.enc1 x1) o1, s1.count + 1⟩)) := by
    simp only [acc, Strat.exp, exp_uniform]
  show |acc (Strat.uniform R fun r => (H.eval (x1, r, m2)).bind (A2 st)) s1 -
    acc (Strat.fwd (H.enc1 x1) fun _ => Strat.uniform D fun d => A2 st d) s1| ≤ _
  rw [hreal, hideal]
  refine (abs_avg_sub_le _ _ _).trans (avg_le hε0 fun o1 ho1 => ?_)
  have hwf2 := hwf1.stepF ho1
  have hlen2 : (s1.trace.stepF (H.enc1 x1) o1).length ≤ q1 + 1 :=
    (Trace.length_stepF_le _ _ _).trans (by omega)
  have hlen2' : ((s1.trace.stepF (H.enc1 x1) o1).length : ℝ) ≤ (q1 : ℝ) + 1 := by
    exact_mod_cast hlen2
  refine (H.hiding_core K hK (H.chop o1) m2 (A2 st) q2 (hA2 st) _ (s1.count + 1) hwf2
    (lt_of_le_of_lt hlen2 hq)).trans ?_
  refine add_le_add (add_le_add ?_ ?_) ?_
  · exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  · exact div_le_div_of_nonneg_left (by positivity) hpos (by linarith)
  · exact div_le_div_of_nonneg_right hlen2' (Nat.cast_nonneg _)

set_option exponentiation.threshold 2000 in
/-- **Hiding at the design's sizes.** State 1,600 bits, salt 128 bits, digest 256 bits: the real
and ideal experiments differ by at most `(q1 + 1 + q2) / 2^127`, where `q1` and `q2` bound the
queries of the two adversary stages. Two worlds (two candidate leaves) therefore differ by at
most `(q1 + 1 + q2) / 2^126`. -/
theorem hiding_1600 [Fintype R] [Nonempty R] [Fintype D] [Nonempty D] [DecidableEq D]
    (hS : Fintype.card S = 2 ^ 1600) (hR : Fintype.card R = 2 ^ 128)
    (hD : Fintype.card D = 2 ^ 256)
    (K : ℕ) (hK : ∀ d : D, (univ.filter fun s => H.trunc s = d).card = K)
    {σ : Type} (A1 : Strat S (X1 × M2 × σ)) (A2 : σ → D → Strat S Bool) (q1 q2 : ℕ)
    (hA1 : A1.QB q1) (hA2 : ∀ st d, (A2 st d).QB q2) (hq1 : q1 + 1 ≤ 2 ^ 1599) :
    |(H.hidingReal A1 A2).prob PState.init (fun b _ => b = true) -
        (H.hidingIdeal A1 A2).prob PState.init (fun b _ => b = true)| ≤
      ((q1 : ℝ) + 1 + q2) / 2 ^ 127 := by
  have hlt : q1 + 1 < Fintype.card S := by
    rw [hS]
    exact lt_of_le_of_lt hq1 (Nat.pow_lt_pow_right (by norm_num) (by norm_num))
  refine (H.hiding_bound K hK A1 A2 q1 q2 hA1 hA2 hlt).trans ?_
  rw [hS, hR, hD]
  push_cast
  have hx : ((q1 : ℝ) + 1) ≤ 2 ^ 1599 := by exact_mod_cast hq1
  have hx0 : (0 : ℝ) ≤ (q1 : ℝ) + 1 := by positivity
  have hy0 : (0 : ℝ) ≤ (q2 : ℝ) := Nat.cast_nonneg _
  generalize (q1 : ℝ) + 1 = x at hx hx0 ⊢
  generalize (q2 : ℝ) = y at hy0 ⊢
  have e1 : (2 : ℝ) ^ 1600 = 2 * 2 ^ 1599 := by
    rw [show (1600 : ℕ) = 1599 + 1 from rfl, pow_succ]
    ring
  have e385 : (2 : ℝ) ^ 256 * 2 ^ 129 = 2 ^ 385 := by rw [← pow_add]
  have h385 : (2 : ℝ) ^ 385 ≤ 2 ^ 1599 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h129 : (2 : ℝ) ^ 129 ≤ 2 ^ 1600 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hP : (0 : ℝ) < 2 ^ 1599 := by positivity
  have hpos : (0 : ℝ) < 2 ^ 1600 - x := by rw [e1]; linarith
  have t2 : y * 2 ^ 256 / (2 ^ 1600 - x) ≤ y / 2 ^ 129 := by
    rw [div_le_div_iff₀ hpos (by positivity)]
    calc y * 2 ^ 256 * 2 ^ 129 = y * 2 ^ 385 := by rw [mul_assoc, e385]
      _ ≤ y * (2 ^ 1600 - x) := by
          apply mul_le_mul_of_nonneg_left _ hy0
          rw [e1]
          linarith
  have t3 : x / 2 ^ 1600 ≤ x / 2 ^ 129 := div_le_div_of_nonneg_left hx0 (by positivity) h129
  have a1 : (x + y) / 2 ^ 128 = (x + y) / 2 ^ 127 / 2 := by
    rw [div_div]
    norm_num
  have a2 : (x + y) / 2 ^ 129 = (x + y) / 2 ^ 127 / 4 := by
    rw [div_div]
    norm_num
  have a3 : y / 2 ^ 129 + x / 2 ^ 129 = (x + y) / 2 ^ 129 := by ring
  have z0 : 0 ≤ (x + y) / 2 ^ 127 := div_nonneg (by linarith) (by positivity)
  linarith

end TwoCall

end CommitGolfCandidate.Permutation
