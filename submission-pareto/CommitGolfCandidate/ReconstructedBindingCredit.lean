import CommitGolfCandidate.ReconstructedBindingMargin

namespace CommitGolfCandidate.Reconstruction.Binding

set_option exponentiation.threshold 2100
set_option maxHeartbeats 700000

/-- The first quadratic term bills completed chains and permutation queries.
The smaller term covers full-digest equality and a previously guessed
continuation key, including a self-link. Two virtual slots cover tiny counts. -/
noncomputable def credit (n c : ℝ) := (320512*(n+2)^2 + 4*(c+1)^2)/2^257

theorem credit_nonneg (n c : ℝ) : 0 ≤ credit n c := by unfold credit; positivity

theorem credit_mono {n m c e : ℝ} (n0 : 0 ≤ n) (c0 : 0 ≤ c) (nm : n ≤ m) (ce : c ≤ e) :
    credit n c ≤ credit m e := by unfold credit; gcongr

noncomputable def increment (n c w : ℝ) := credit (n+w) (c+1) - credit n c

noncomputable def hazard (n c w : ℝ) := (320147*(n+2)*w + 2*c+1)/2^256

theorem increment_nonneg {n c w : ℝ} (hn : 0 ≤ n) (hc : 0 ≤ c) (hw : 0 ≤ w) :
    0 ≤ increment n c w := sub_nonneg.mpr (credit_mono hn hc (by linarith) (by linarith))

theorem hazard_le_loss {n c w : ℝ} (hn : 0 ≤ n) (hc : 0 ≤ c) (hw : 0 ≤ w)
    (nmax : n ≤ 2^121) (cmax : c ≤ 2^121) (wmax : w ≤ 9) :
    hazard n c w ≤ 1 - Real.exp (-increment n c w) := by
  let delta := increment n c w
  have nonneg : 0 ≤ delta := increment_nonneg hn hc hw
  have upper : delta ≤ 1/4096 := by
    -- Subtract the old credit before bounding products. The credit itself
    -- can exceed one, whereas its one-step increment is very small.
    have nw := mul_le_mul nmax wmax hw (by positivity : (0:ℝ) ≤ 2^121)
    have ww := mul_le_mul wmax wmax hw (by norm_num : (0:ℝ) ≤ 9)
    unfold delta increment credit
    norm_num at nw ww ⊢
    nlinarith only [nw,ww,cmax,wmax]
  have headroom : hazard n c w*(1+1/4096) ≤ delta := by
    unfold delta increment credit hazard
    have t : 0 ≤ n*w := mul_nonneg hn hw
    nlinarith [sq_nonneg w]
  have h0 : 0 ≤ hazard n c w := by unfold hazard; positivity
  have ratio : hazard n c w ≤ delta/(1+delta) :=
    (le_div_iff₀ (by linarith)).2 ((mul_le_mul_of_nonneg_left (by linarith : 1+delta ≤ 1+1/4096) h0).trans headroom)
  have invExp : Real.exp (-delta) ≤ 1/(1+delta) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp delta])
  change hazard n c w ≤ 1 - Real.exp (-delta)
  calc
    _ ≤ delta/(1+delta) := ratio
    _ = 1-1/(1+delta) := by field_simp; ring
    _ ≤ _ := by linarith

noncomputable def cap (Q : Nat) := credit ((Q:ℝ)+9) ((Q:ℝ)+1)

/-- The common survival envelope fits the query contract even when the two
checker replays contribute up to 2^32 extra rows. -/
theorem cap_margin (q Q : Nat) (hq : 1 ≤ q) (small : q < 2^120) (replay : Q ≤ q+2^32) :
    1-Real.exp (-cap Q) ≤ (q:ℝ)/2^120 := by
  have qlo : (1:ℝ) ≤ q := by exact_mod_cast hq
  have qhi : (q:ℝ) ≤ 2^120 := by exact_mod_cast small.le
  have Qhi : (Q:ℝ) ≤ q + 2^32 := by exact_mod_cast replay
  by_cases low : q ≤ 2^50
  · have limit : (Q:ℝ) ≤ 2^51 := by exact_mod_cast (show Q ≤ 2^51 by omega)
    have bound := credit_mono (n := (Q:ℝ)+9) (m := 2^51+9) (c := (Q:ℝ)+1) (e := 2^51+1)
      (by positivity) (by positivity) (by linarith) (by linarith)
    have enough : credit (2^51+9) (2^51+1) ≤ (1:ℝ)/2^120 := by norm_num [credit]
    have final : cap Q ≤ (q:ℝ)/2^120 := bound.trans (enough.trans (by gcongr))
    linarith [Real.add_one_le_exp (-cap Q)]
  · let x : ℝ := (q:ℝ)/2^120
    have lo : (2:ℝ)^50 ≤ q := by exact_mod_cast (show 2^50 ≤ q by omega)
    have inflated : (Q:ℝ)+11 ≤ (q:ℝ)*(100001/100000) := by nlinarith
    have bound₁ := mul_self_le_mul_self (by positivity : 0 ≤ (Q:ℝ)+11) inflated
    have bound₂ := mul_self_le_mul_self (by positivity : 0 ≤ (Q:ℝ)+2) (by linarith : (Q:ℝ)+2 ≤ (q:ℝ)*(100001/100000))
    have capLe : cap Q ≤ (245/100)*x^2 := by
      unfold cap credit x
      nlinarith only [bound₁,bound₂,sq_nonneg (q:ℝ)]
    have ex := Real.exp_le_exp.mpr (neg_le_neg capLe)
    have target := weighted_survival_margin x (by dsimp [x]; positivity) (by dsimp [x]; norm_num; linarith)
    rw [neg_mul] at target
    change _ ≤ x
    linarith only [target,ex]

end CommitGolfCandidate.Reconstruction.Binding
