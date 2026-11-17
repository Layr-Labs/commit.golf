import CommitGolfCandidate.S3LeafLayout

/-!
# The leaf-collision game in the lazy permutation model

An adversary strategy outputs a list of leaves; the game then evaluates the two-call leaf hash on
each of them (two forward queries per leaf, no inverse query). `ProbeCollision` says that two of
the evaluated leaves have different hash inputs and the same digest.

* `TwoCall.overlap_probe_collision_bound`: for an adversary with at most `q` queries and at most
  `e` probed leaves, all valid for the overlap, the collision probability is at most
  `unionBound |S| (Kd + 2 Kc + K2 + 2 Ko) K2 (q + 2e)` (S3Overlap.lean).
* `s3EvalList`, `S3Collides`, `s3_collision_prob_le`: the same at the stage-3 sizes, where the
  bound is at most `(q + 2e)^2 / 2^256 + q / 2^127` for `q ≤ 2^120` and `e ≤ 2^26`.
-/

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 2100

namespace CommitGolfCandidate.Permutation

open Finset

variable {S : Type} [Fintype S] [DecidableEq S]

namespace TwoCall

variable {X1 R C M2 D : Type} (H : TwoCall S X1 R C M2 D)

/-- Evaluate the leaf hash on each item in turn; `f` maps an item to its hash input. -/
def probe {ι : Type} (f : ι → X1 × R × M2) : List ι → Strat S (List (ι × D))
  | [] => .done []
  | i :: rest => (H.eval (f i)).bind fun d => (probe f rest).bind fun out => .done ((i, d) :: out)

theorem probe_post {ι : Type} (f : ι → X1 × R × M2) (items : List ι) (s : PState S)
    (hs : s.trace.WF) :
    (H.probe f items).post s fun out s' =>
      s'.trace.WF ∧ s.trace <:+ s'.trace ∧ out.map Prod.fst = items ∧
        ∀ p ∈ out, H.Evaluates s'.trace (f p.1) p.2 := by
  induction items generalizing s with
  | nil => exact ⟨hs, List.suffix_refl _, rfl, by simp⟩
  | cons i rest ih =>
    show ((H.eval (f i)).bind fun d => (H.probe f rest).bind fun out => .done ((i, d) :: out)).post
      s _
    refine Strat.post_bind (Strat.post_mono ?_ (H.eval_post (f i) s hs))
    rintro d s1 ⟨hwf1, hsuf1, hev⟩
    refine Strat.post_bind (Strat.post_mono ?_ (ih s1 hwf1))
    rintro out s2 ⟨hwf2, hsuf2, hmap, hall⟩
    refine ⟨hwf2, hsuf1.trans hsuf2, by simp [hmap], fun p hp => ?_⟩
    rcases List.mem_cons.1 hp with rfl | h
    · exact Evaluates.mono H hsuf2 hev
    · exact hall p h

theorem probe_QB {ι : Type} (f : ι → X1 × R × M2) (items : List ι) :
    (H.probe f items).QB (2 * items.length) := by
  induction items with
  | nil => exact .done _ _
  | cons i rest ih =>
    have h := Strat.QB.bind (H.eval_QB (f i)) fun d =>
      Strat.QB.bind ih fun out => Strat.QB.done ((i, d) :: out) 0
    exact h.mono (by simp only [List.length_cons]; omega)

/-- Two probed items with different hash inputs and the same digest. -/
def ProbeCollision {ι : Type} (f : ι → X1 × R × M2) (out : List (ι × D)) : Prop :=
  ∃ a ∈ out, ∃ b ∈ out, f a.1 ≠ f b.1 ∧ a.2 = b.2

/-- **Collision among probed leaves, overlap layout.** The adversary makes at most `q` queries
(forward or inverse) and outputs a list of items; the first `e` of them are hashed. Every item
maps to a valid leaf input (`ovA x1 = ovM m2`). -/
theorem overlap_probe_collision_bound [Fintype X1] [Fintype R] [Fintype M2] [DecidableEq C]
    [DecidableEq D] {O : Type} [DecidableEq O] (ovA : X1 → O) (ovM : M2 → O)
    {ι : Type} (f : ι → X1 × R × M2) (hf : ∀ i, ovA (f i).1 = ovM (f i).2.2)
    (Kd Kc K2 Ko q e : ℕ) (hQ : q + 2 * e < Fintype.card S)
    (hKd : ∀ d : D, (univ.filter fun s => H.trunc s = d).card ≤ Kd)
    (hKc : ∀ c : C, (univ.filter fun s => H.chop s = c).card ≤ Kc)
    (hK2 : Fintype.card R * Fintype.card M2 ≤ K2)
    (hKo : ∀ o : O, (univ.filter fun x : X1 => ovA x = o).card ≤ Ko)
    (A : Strat S (List ι)) (hA : A.QB q) :
    (A.bind fun items => H.probe f (items.take e)).prob PState.init
        (fun out _ => ProbeCollision f out) ≤
      unionBound (Fintype.card S) (Kd + 2 * Kc + K2 + 2 * Ko) K2 (q + 2 * e) := by
  have hQB : (A.bind fun items => H.probe f (items.take e)).QB (q + 2 * e) :=
    Strat.QB.bind hA fun items => (H.probe_QB f (items.take e)).mono (by
      have := List.length_take_le e items
      omega)
  have hpost : (A.bind fun items => H.probe f (items.take e)).post PState.init fun out s' =>
      (∀ p ∈ out, H.Evaluates s'.trace (f p.1) p.2) ∧
        (s'.trace.length ≤ (PState.init : PState S).trace.length + (q + 2 * e) ∧
          s'.count ≤ (PState.init : PState S).count + (q + 2 * e)) := by
    refine Strat.post_and ?_ (Strat.post_QB hQB PState.init)
    refine Strat.post_bind (Strat.post_mono ?_ (Strat.post_inv A PState.init Trace.WF.nil))
    rintro items s1 ⟨hwf1, -, -⟩
    exact Strat.post_mono (fun out s' h => h.2.2.2) (H.probe_post f (items.take e) s1 hwf1)
  refine (Strat.prob_le_prob_of_post hpost ?_).trans
    (H.overlap_prob_not_good_le ovA ovM Kd Kc K2 Ko (q + 2 * e) hQ hKd hKc hK2 hKo _)
  rintro out s' ⟨hev, -, hc⟩ ⟨a, ha, b, hb, hne, heq⟩
  refine ⟨H.overlap_collision_imp_bad ovA ovM hne (hf a.1) (hf b.1) (hev a ha) ?_,
    by simpa [PState.init] using hc⟩
  rw [heq]
  exact hev b hb

end TwoCall

/-! ### The stage-3 sizes -/

/-- Evaluate every item with `s3TwoCall.eval` (two forward queries each), keeping the item. -/
def s3EvalList {ι : Type} (inp : ι → S3LeafInput) : List ι → Strat S3State (List (ι × BitVec 256))
  | [] => .done []
  | i :: rest => (s3TwoCall.eval (inp i)).bind fun d =>
      (s3EvalList inp rest).bind fun out => .done ((i, d) :: out)

theorem s3EvalList_eq_probe {ι : Type} (inp : ι → S3LeafInput) (items : List ι) :
    s3EvalList inp items = s3TwoCall.probe inp items := by
  induction items with
  | nil => rfl
  | cons i rest ih => simp only [s3EvalList, TwoCall.probe, ih]

/-- Two evaluated items with different hash inputs and the same digest. -/
def S3Collides {ι : Type} (inp : ι → S3LeafInput) (out : List (ι × BitVec 256)) : Prop :=
  ∃ a ∈ out, ∃ b ∈ out, inp a.1 ≠ inp b.1 ∧ a.2 = b.2

/-- **Leaf collisions in the lazy permutation model, stage-3 sizes.** An adversary with at most
`q` permutation queries (forward or inverse) outputs items; the first `extra` are hashed with two
forward queries each. Every item maps to a valid leaf input. Two hashed items with different
inputs and one digest appear with probability at most `(q + 2 extra)^2 / 2^256 + q / 2^127`. -/
theorem s3_collision_prob_le {ι : Type} (inp : ι → S3LeafInput)
    (valid : ∀ i, s3OvA (inp i).1 = s3OvM (inp i).2.2) (A : Strat S3State (List ι))
    (q extra : ℕ) (hA : A.QB q) (hq : q ≤ 2 ^ 120) (hextra : extra ≤ 2 ^ 26) :
    (A.bind fun items => s3EvalList inp (items.take extra)).prob PState.init
        (fun out _ => S3Collides inp out) ≤
      ((q : ℝ) + 2 * extra) ^ 2 / 2 ^ 256 + (q : ℝ) / 2 ^ 127 := by
  have hsmall : q + 2 * extra ≤ 2 ^ 128 := by
    have h1 : (2 : ℕ) ^ 120 + 2 * 2 ^ 26 ≤ 2 ^ 128 := by norm_num
    omega
  have hQ : q + 2 * extra < Fintype.card S3State := by
    rw [s3_card_state]
    exact lt_of_le_of_lt hsmall (Nat.pow_lt_pow_right (by norm_num) (by norm_num))
  have h := s3TwoCall.overlap_probe_collision_bound s3OvA s3OvM inp valid (2 ^ 1344) (2 ^ 1152)
    (2 ^ 1152) (2 ^ 1088) q extra hQ s3_trunc_fiber s3_chop_fiber s3_second_inputs
    s3_overlap_fiber A hA
  simp only [s3EvalList_eq_probe]
  exact h.trans (s3_union_bound_le q extra hsmall)

end CommitGolfCandidate.Permutation
