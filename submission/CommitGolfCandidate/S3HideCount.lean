import CommitGolfCandidate.S3HideLayout
import CommitGolfCandidate.S3PermHiding

/-! Lazy-model hiding at the stage-3 sizes: every digest has exactly `2^1344` preimages, the
hiding experiments are averages over the nonce (digest) of experiments with a fixed nonce
(digest), and the hiding bound reads `2 (q1 + 1 + q2) / 2^192`. Mathlib only. -/

set_option exponentiation.threshold 2100

namespace CommitGolfCandidate.Permutation

open Finset

namespace Strat

variable {S : Type} [Fintype S] [DecidableEq S] {α : Type}

/-- Expectation commutes with a finite average of the payoff. -/
theorem exp_avg {κ : Type} (I : Finset κ) (F : κ → α → PState S → ℝ) (st : Strat S α)
    (s : PState S) :
    st.exp s (fun a s' => avg I fun j => F j a s') = avg I fun j => st.exp s (F j) := by
  induction st generalizing s with
  | done a => rfl
  | fwd x k ih =>
    simp only [exp, ih]
    exact avg_comm _ _ _
  | inv y k ih =>
    simp only [exp, ih]
    exact avg_comm _ _ _
  | rand n k ih =>
    simp only [exp, ih]
    exact avg_comm _ _ _

end Strat

namespace TwoCall

variable {S : Type} [Fintype S] [DecidableEq S]
variable {X1 R C M2 D : Type} (H : TwoCall S X1 R C M2 D)

/-- The real experiment is the average over the nonce of the experiment with that nonce. -/
theorem hiding_real_avg [Fintype R] [Nonempty R] {σ : Type}
    (A1 : Strat S (X1 × M2 × σ)) (A2 : σ → D → Strat S Bool) (s : PState S)
    (E : Bool → PState S → Prop) :
    (H.hidingReal A1 A2).prob s E =
      avg univ fun r : R =>
        (A1.bind fun a => (H.eval (a.1, r, a.2.1)).bind (A2 a.2.2)).prob s E := by
  unfold hidingReal Strat.prob
  rw [Strat.exp_bind]
  simp only [Strat.exp_uniform]
  rw [Strat.exp_avg]
  refine avg_congr fun r _ => ?_
  rw [Strat.exp_bind]

/-- The ideal experiment is the average over the digest of the experiment with that digest. -/
theorem hiding_ideal_avg [Fintype D] [Nonempty D] {σ : Type}
    (A1 : Strat S (X1 × M2 × σ)) (A2 : σ → D → Strat S Bool) (s : PState S)
    (E : Bool → PState S → Prop) :
    (H.hidingIdeal A1 A2).prob s E =
      avg univ fun d : D =>
        (A1.bind fun a => Strat.fwd (H.enc1 a.1) fun _ => A2 a.2.2 d).prob s E := by
  unfold hidingIdeal Strat.prob
  rw [Strat.exp_bind]
  have inner : ∀ (a : X1 × M2 × σ) (s1 : PState S),
      (Strat.fwd (H.enc1 a.1) fun _ => Strat.uniform D fun d => A2 a.2.2 d).exp s1
          (fun b s' => ind (E b s')) =
        avg univ fun d : D =>
          (Strat.fwd (H.enc1 a.1) fun _ => A2 a.2.2 d).exp s1 (fun b s' => ind (E b s')) := by
    intro a s1
    simp only [Strat.exp, Strat.exp_uniform]
    exact avg_comm _ _ _
  simp only [inner]
  rw [Strat.exp_avg]
  refine avg_congr fun d _ => ?_
  rw [Strat.exp_bind]

end TwoCall

end CommitGolfCandidate.Permutation

namespace CommitGolfCandidate

open CommitGolf Permutation Finset

/-- Every digest has exactly `2^1344` preimages among the 1600-bit states. -/
theorem s3_trunc_regular (d : BitVec 256) :
    (univ.filter fun s : S3State => s3TwoCall.trunc s = d).card = 2 ^ 1344 := by
  by_contra h
  have hlt : (univ.filter fun s : S3State => s3TwoCall.trunc s = d).card < 2 ^ 1344 :=
    lt_of_le_of_ne (s3_trunc_fiber d) h
  have hsum : (univ : Finset S3State).card =
      ∑ b ∈ (univ : Finset (BitVec 256)),
        (univ.filter fun s : S3State => s3TwoCall.trunc s = b).card :=
    Finset.card_eq_sum_card_fiberwise (by intro x _; simp)
  have hlt2 : ∑ b ∈ (univ : Finset (BitVec 256)),
        (univ.filter fun s : S3State => s3TwoCall.trunc s = b).card <
      ∑ _b ∈ (univ : Finset (BitVec 256)), 2 ^ 1344 :=
    Finset.sum_lt_sum (fun b _ => s3_trunc_fiber b) ⟨d, Finset.mem_univ _, hlt⟩
  rw [← hsum, Finset.card_univ, s3_card_state, Finset.sum_const, Finset.card_univ,
    s3_card_bitvec, smul_eq_mul, ← pow_add] at hlt2
  exact absurd hlt2 (lt_irrefl _)

/-- The lazy-model hiding bound at the stage-3 sizes (1600-bit state, 192-bit nonce,
256-bit digest). -/
theorem s3_strat_hiding {σ : Type} (A1 : Strat S3State (BitVec 1600 × BitVec 704 × σ))
    (A2 : σ → BitVec 256 → Strat S3State Bool) (q1 q2 : ℕ)
    (hA1 : A1.QB q1) (hA2 : ∀ st d, (A2 st d).QB q2) (hq1 : q1 + 1 ≤ 2 ^ 1599) :
    |(s3TwoCall.hidingReal A1 A2).prob PState.init (fun b _ => b = true) -
        (s3TwoCall.hidingIdeal A1 A2).prob PState.init (fun b _ => b = true)| ≤
      2 * ((q1 : ℝ) + 1 + q2) / 2 ^ 192 := by
  have hlt : q1 + 1 < Fintype.card S3State := by
    rw [s3_card_state]
    exact lt_of_le_of_lt hq1 (Nat.pow_lt_pow_right (by norm_num) (by norm_num))
  refine (s3TwoCall.hiding_bound (2 ^ 1344) s3_trunc_regular A1 A2 q1 q2 hA1 hA2 hlt).trans ?_
  have hS : Fintype.card S3State = 2 ^ 1600 := s3_card_state
  have hR : Fintype.card (BitVec 192) = 2 ^ 192 := s3_card_bitvec 192
  have hD : Fintype.card (BitVec 256) = 2 ^ 256 := s3_card_bitvec 256
  rw [hS, hR, hD]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hx : ((q1 : ℝ) + 1) ≤ 2 ^ 1599 := by exact_mod_cast hq1
  have hx0 : (0 : ℝ) ≤ (q1 : ℝ) + 1 := by positivity
  have hy0 : (0 : ℝ) ≤ (q2 : ℝ) := Nat.cast_nonneg _
  generalize (q1 : ℝ) + 1 = x at hx hx0 ⊢
  generalize (q2 : ℝ) = y at hy0 ⊢
  have e1 : (2 : ℝ) ^ 1600 = 2 * 2 ^ 1599 := by
    rw [show (1600 : ℕ) = 1599 + 1 from rfl, pow_succ]
    ring
  have e449 : (2 : ℝ) ^ 256 * 2 ^ 193 = 2 ^ 449 := by rw [← pow_add]
  have h449 : (2 : ℝ) ^ 449 ≤ 2 ^ 1599 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have h193 : (2 : ℝ) ^ 193 ≤ 2 ^ 1600 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hP : (0 : ℝ) < 2 ^ 1599 := by positivity
  have hpos : (0 : ℝ) < 2 ^ 1600 - x := by rw [e1]; linarith
  have t2 : y * 2 ^ 256 / (2 ^ 1600 - x) ≤ y / 2 ^ 193 := by
    rw [div_le_div_iff₀ hpos (by positivity)]
    calc y * 2 ^ 256 * 2 ^ 193 = y * 2 ^ 449 := by rw [mul_assoc, e449]
      _ ≤ y * (2 ^ 1600 - x) := by
          apply mul_le_mul_of_nonneg_left _ hy0
          rw [e1]
          linarith
  have t3 : x / 2 ^ 1600 ≤ x / 2 ^ 193 := div_le_div_of_nonneg_left hx0 (by positivity) h193
  have a2 : (x + y) / 2 ^ 193 = (x + y) / 2 ^ 192 / 2 := by
    rw [div_div]
    norm_num
  have a3 : y / 2 ^ 193 + x / 2 ^ 193 = (x + y) / 2 ^ 193 := by ring
  have a4 : 2 * (x + y) / 2 ^ 192 = 2 * ((x + y) / 2 ^ 192) := by ring
  have z0 : 0 ≤ (x + y) / 2 ^ 192 := div_nonneg (by linarith) (by positivity)
  calc (x + y) / 2 ^ 192 + y * 2 ^ 256 / (2 ^ 1600 - x) + x / 2 ^ 1600
      ≤ (x + y) / 2 ^ 192 + y / 2 ^ 193 + x / 2 ^ 193 := add_le_add (add_le_add le_rfl t2) t3
    _ = (x + y) / 2 ^ 192 + (x + y) / 2 ^ 192 / 2 := by rw [add_assoc, a3, a2]
    _ ≤ 2 * ((x + y) / 2 ^ 192) := by
        generalize (x + y) / 2 ^ 192 = z at z0
        linarith
    _ = 2 * (x + y) / 2 ^ 192 := a4.symm

end CommitGolfCandidate
