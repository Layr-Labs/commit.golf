import CommitGolfCandidate.Stage3cSurvival

/-! Finite shifted survival arithmetic with a full 32-bit verifier replay. -/
namespace CommitGolfCandidate.Chained.Reserve
open CommitGolfCandidate

set_option exponentiation.threshold 2100
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

noncomputable def exponent (m : ℝ) : ℝ := m^2/(2*(2^238-16*m))

theorem exponent_le (q m hi : ℝ) (hq : q ≤ hi*2^120)
    (hm : m ≤ q+2^33) (m0 : 0 ≤ m) (q0 : 0 ≤ q)
    (hlo : 1/4 ≤ hi) (hhi : hi ≤ 2) :
    exponent m ≤ 2*hi^2*(1001/1000) := by
  have mUp : m ≤ hi*2^120+2^33 := by linarith
  have mSmall : m ≤ 2^122 := by nlinarith
  have gap : 2^238*(1-1/2^111) ≤ (2:ℝ)^238-16*m := by nlinarith
  have gapPos : (0:ℝ) < 2^238-16*m := by
    have far : (0:ℝ) < 2^238-16*2^122 := by norm_num
    linarith
  unfold exponent
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*(2^238-16*m))]
  have sq : m^2 ≤ (hi*2^120+2^33)^2 := by nlinarith
  have expand : (hi*2^120+2^33)^2 ≤ hi^2*2^240*(1+1/2^80) := by nlinarith
  have hi2 : 0 ≤ hi^2 := sq_nonneg hi
  have key : hi^2*2^240*(1+1/2^80) ≤
      hi^2*(1001/1000)*(2^240*(1-1/2^111)) := by
    have c : (1:ℝ)+1/2^80 ≤ (1001/1000)*(1-1/2^111) := by norm_num
    nlinarith
  have scaled := mul_le_mul_of_nonneg_left gap (by positivity : (0:ℝ) ≤ 4*hi^2*(1001/1000))
  nlinarith

theorem small_budget (q m lo : ℝ) (q1 : 1 ≤ q) (hq : q ≤ lo*2^120)
    (hm : m ≤ q+2^33) (m0 : 0 ≤ m) (lo1 : lo ≤ 1)
    (room : (lo+1/2^50)*2^240 ≤ 959/512*2^238*(1-1/2^111)) :
    1-Real.exp (-exponent m) ≤ (959/1024)*(q/2^120) := by
  have q0 : 0 ≤ q := by linarith
  have mSmall : m ≤ 2^121 := by nlinarith
  have gap : 2^238*(1-1/2^111) ≤ (2:ℝ)^238-16*m := by nlinarith
  have gapPos : (0:ℝ) < 2^238-16*m := by
    have far : (0:ℝ) < 2^238-16*2^121 := by norm_num
    linarith
  have lin : 1-Real.exp (-exponent m) ≤ exponent m := by
    linarith [Real.add_one_le_exp (-exponent m)]
  refine lin.trans ?_
  unfold exponent
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*(2^238-16*m))]
  have m2 : m*m ≤ (q+2^33)*(q+2^33) := mul_self_le_mul_self m0 hm
  have qq : q*q ≤ q*(lo*2^120) := mul_le_mul_of_nonneg_left hq q0
  have lin2 : 2*2^33*q+2^66 ≤ q*2^67 := by nlinarith
  have sq : m^2 ≤ q*(lo*2^120+2^67) := by nlinarith
  have inner : lo*2^120+2^67 ≤ 959/512*(2^238-16*m)/2^120 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have scaled := mul_le_mul_of_nonneg_left inner q0
  have eq : 959/1024*(q/2^120)*(2*(2^238-16*m)) =
      q*(959/512*(2^238-16*m)/2^120) := by ring
  linarith

theorem survival_margin (q : Nat) (positive : 1 ≤ q) (small : (q:ℝ) ≤ (11/10)*2^120) :
    1-Real.exp (-exponent ((q+2^32+1 : Nat) : ℝ)) ≤ (959/1024)*((q:ℝ)/2^120) := by
  let m : ℝ := ((q+2^32+1 : Nat) : ℝ)
  have q1 : (1:ℝ) ≤ q := by exact_mod_cast positive
  have qs : (q:ℝ) ≤ (11/10)*2^120 := small
  have mR : m ≤ (q:ℝ)+2^33 := by dsimp [m]; push_cast; linarith
  have m0 : 0 ≤ m := by positivity
  have piece : ∀ lo hi u : ℝ, lo*2^120 ≤ q → (q:ℝ) ≤ hi*2^120 →
      1/4 ≤ hi → hi ≤ 2 → 2*hi^2*(1001/1000) ≤ u → u ≤ ((64:Nat):ℝ) →
      1-(1-u/((64:Nat):ℝ))^64 ≤ (959/1024)*lo →
      1-Real.exp (-exponent m) ≤ (959/1024)*((q:ℝ)/2^120) := by
    intro lo hi u hl hh h4 h1 hu hu64 check
    exact interval_step _ _ _ lo u 64
      ((exponent_le _ _ _ hh mR m0 (by linarith) h4 h1).trans hu) hu64 (by norm_num)
      (by rw [le_div_iff₀ (by positivity)]; linarith) (by norm_num) check
  by_cases h0 : (q:ℝ) ≤ (2/5)*2^120
  · exact small_budget _ _ (2/5) q1 h0 mR m0 (by norm_num) (by norm_num)
  by_cases h21 : (q:ℝ) ≤ (21/50)*2^120
  · exact piece (20/50) (21/50) (441441/1250000) (by linarith) h21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h21 := le_of_lt (not_le.mp h21)
  by_cases h22 : (q:ℝ) ≤ (22/50)*2^120
  · exact piece (21/50) (22/50) (484484/1250000) (by linarith) h22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h22 := le_of_lt (not_le.mp h22)
  by_cases h23 : (q:ℝ) ≤ (23/50)*2^120
  · exact piece (22/50) (23/50) (529529/1250000) (by linarith) h23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h23 := le_of_lt (not_le.mp h23)
  by_cases h24 : (q:ℝ) ≤ (24/50)*2^120
  · exact piece (23/50) (24/50) (576576/1250000) (by linarith) h24 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h24 := le_of_lt (not_le.mp h24)
  by_cases h25 : (q:ℝ) ≤ (25/50)*2^120
  · exact piece (24/50) (25/50) (625625/1250000) (by linarith) h25 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h25 := le_of_lt (not_le.mp h25)
  by_cases h26 : (q:ℝ) ≤ (26/50)*2^120
  · exact piece (25/50) (26/50) (676676/1250000) (by linarith) h26 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h26 := le_of_lt (not_le.mp h26)
  by_cases h27 : (q:ℝ) ≤ (27/50)*2^120
  · exact piece (26/50) (27/50) (729729/1250000) (by linarith) h27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h27 := le_of_lt (not_le.mp h27)
  by_cases h28 : (q:ℝ) ≤ (28/50)*2^120
  · exact piece (27/50) (28/50) (784784/1250000) (by linarith) h28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h28 := le_of_lt (not_le.mp h28)
  by_cases h29 : (q:ℝ) ≤ (29/50)*2^120
  · exact piece (28/50) (29/50) (841841/1250000) (by linarith) h29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h29 := le_of_lt (not_le.mp h29)
  by_cases h30 : (q:ℝ) ≤ (30/50)*2^120
  · exact piece (29/50) (30/50) (900900/1250000) (by linarith) h30 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h30 := le_of_lt (not_le.mp h30)
  by_cases h31 : (q:ℝ) ≤ (31/50)*2^120
  · exact piece (30/50) (31/50) (961961/1250000) (by linarith) h31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h31 := le_of_lt (not_le.mp h31)
  by_cases h32 : (q:ℝ) ≤ (32/50)*2^120
  · exact piece (31/50) (32/50) (1025024/1250000) (by linarith) h32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h32 := le_of_lt (not_le.mp h32)
  by_cases h33 : (q:ℝ) ≤ (33/50)*2^120
  · exact piece (32/50) (33/50) (1090089/1250000) (by linarith) h33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h33 := le_of_lt (not_le.mp h33)
  by_cases h34 : (q:ℝ) ≤ (34/50)*2^120
  · exact piece (33/50) (34/50) (1157156/1250000) (by linarith) h34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h34 := le_of_lt (not_le.mp h34)
  by_cases h35 : (q:ℝ) ≤ (35/50)*2^120
  · exact piece (34/50) (35/50) (1226225/1250000) (by linarith) h35 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h35 := le_of_lt (not_le.mp h35)
  by_cases h36 : (q:ℝ) ≤ (36/50)*2^120
  · exact piece (35/50) (36/50) (1297296/1250000) (by linarith) h36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h36 := le_of_lt (not_le.mp h36)
  by_cases h37 : (q:ℝ) ≤ (37/50)*2^120
  · exact piece (36/50) (37/50) (1370369/1250000) (by linarith) h37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h37 := le_of_lt (not_le.mp h37)
  by_cases h38 : (q:ℝ) ≤ (38/50)*2^120
  · exact piece (37/50) (38/50) (1445444/1250000) (by linarith) h38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h38 := le_of_lt (not_le.mp h38)
  by_cases h39 : (q:ℝ) ≤ (39/50)*2^120
  · exact piece (38/50) (39/50) (1522521/1250000) (by linarith) h39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h39 := le_of_lt (not_le.mp h39)
  by_cases h40 : (q:ℝ) ≤ (40/50)*2^120
  · exact piece (39/50) (40/50) (1601600/1250000) (by linarith) h40 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h40 := le_of_lt (not_le.mp h40)
  by_cases h41 : (q:ℝ) ≤ (41/50)*2^120
  · exact piece (40/50) (41/50) (1682681/1250000) (by linarith) h41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h41 := le_of_lt (not_le.mp h41)
  by_cases h42 : (q:ℝ) ≤ (42/50)*2^120
  · exact piece (41/50) (42/50) (1765764/1250000) (by linarith) h42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h42 := le_of_lt (not_le.mp h42)
  by_cases h43 : (q:ℝ) ≤ (43/50)*2^120
  · exact piece (42/50) (43/50) (1850849/1250000) (by linarith) h43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h43 := le_of_lt (not_le.mp h43)
  by_cases h44 : (q:ℝ) ≤ (44/50)*2^120
  · exact piece (43/50) (44/50) (1937936/1250000) (by linarith) h44 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h44 := le_of_lt (not_le.mp h44)
  by_cases h45 : (q:ℝ) ≤ (45/50)*2^120
  · exact piece (44/50) (45/50) (2027025/1250000) (by linarith) h45 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h45 := le_of_lt (not_le.mp h45)
  by_cases h46 : (q:ℝ) ≤ (46/50)*2^120
  · exact piece (45/50) (46/50) (2118116/1250000) (by linarith) h46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h46 := le_of_lt (not_le.mp h46)
  by_cases h47 : (q:ℝ) ≤ (47/50)*2^120
  · exact piece (46/50) (47/50) (2211209/1250000) (by linarith) h47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h47 := le_of_lt (not_le.mp h47)
  by_cases h48 : (q:ℝ) ≤ (48/50)*2^120
  · exact piece (47/50) (48/50) (2306304/1250000) (by linarith) h48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h48 := le_of_lt (not_le.mp h48)
  by_cases h49 : (q:ℝ) ≤ (49/50)*2^120
  · exact piece (48/50) (49/50) (2403401/1250000) (by linarith) h49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h49 := le_of_lt (not_le.mp h49)
  by_cases h50 : (q:ℝ) ≤ 2^120
  · exact piece (49/50) 1 (1001/500) (by linarith) (by simpa using h50) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact piece 1 (11/10) (121121/50000) (by linarith) qs (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem graph_margin (q : Nat) (positive : 1 ≤ q) (small : (q:ℝ) ≤ (11/10)*2^120) :
    (((q+2^32 : Nat) : ℝ)*((q+2^32 : Nat) : ℝ))/2^256 ≤ (1/1024)*((q:ℝ)/2^120) := by
  have q1 : (1:ℝ) ≤ q := by exact_mod_cast positive
  have q0 : (0:ℝ) ≤ q := by positivity
  have qq := mul_le_mul_of_nonneg_left small q0
  have linear : 2*2^32*(q:ℝ)+2^64 ≤ q*2^66 := by nlinarith
  push_cast
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2^256)]
  nlinarith

theorem joint_margin (q : Nat) (positive : 1 ≤ q) (small : (q:ℝ) ≤ (11/10)*2^120) :
    (1-Real.exp (-exponent ((q+2^32+1 : Nat) : ℝ)))+
      (((q+2^32 : Nat) : ℝ)*((q+2^32 : Nat) : ℝ))/2^256 ≤
      (15/16)*((q:ℝ)/2^120) := by
  have a := survival_margin q positive small
  have b := graph_margin q positive small
  linarith

end CommitGolfCandidate.Chained.Reserve
