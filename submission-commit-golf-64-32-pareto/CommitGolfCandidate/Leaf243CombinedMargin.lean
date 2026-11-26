import CommitGolfCandidate.TwoPermutationPinnedLeafWidth

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2100

theorem small_budget_243 (N q m lo : ℝ) (hN : 2 ^ 238 ≤ N) (q1 : 1 ≤ q) (hq : q ≤ lo * 2 ^ 120)
    (hm : m ≤ q + 2 ^ 31) (m0 : 0 ≤ m) (lo1 : lo ≤ 1)
    (room : (lo + 1 / 2 ^ 50) * 2 ^ 240 ≤ 959 / 512 * N * (1 - 1 / 2 ^ 116)) :
    1 - Real.exp (-collisionExponent N m) ≤ 959 / 1024 * (q / 2 ^ 120) := by
  have q0 : 0 ≤ q := by linarith
  have mSmall : m ≤ 2 ^ 121 := by nlinarith
  have Npos : 0 < N := by linarith
  have far : (2 : ℝ) ^ 121 < 2 ^ 238 := by norm_num
  have gapPos : 0 < N - m := by linarith
  have lin : 1 - Real.exp (-collisionExponent N m) ≤ collisionExponent N m := by
    linarith [Real.add_one_le_exp (-collisionExponent N m)]
  refine lin.trans ?_
  unfold collisionExponent
  rw [div_div, div_le_iff₀ (by linarith)]
  have mm : m * (m - 1) ≤ m * m := by nlinarith
  have m2 : m * m ≤ (q + 2 ^ 31) * (q + 2 ^ 31) := mul_self_le_mul_self m0 hm
  have qq : q * q ≤ q * (lo * 2 ^ 120) := mul_le_mul_of_nonneg_left hq q0
  have lin2 : 2 * 2 ^ 31 * q + 2 ^ 62 ≤ q * 2 ^ 63 := by nlinarith
  have sq : m * (m - 1) ≤ q * (lo * 2 ^ 120 + 2 ^ 63) := by nlinarith
  have gap : N * (1 - 1 / 2 ^ 116) ≤ N - m := by
    have : (2 : ℝ) ^ 121 ≤ N * (1 / 2 ^ 116) := by
      have h : (2 : ℝ) ^ 121 ≤ 2 ^ 238 * (1 / 2 ^ 116) := by norm_num
      nlinarith
    linarith
  have inner : lo * 2 ^ 120 + 2 ^ 63 ≤ 959 / 512 * (N - m) / 2 ^ 120 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have scaled := mul_le_mul_of_nonneg_left inner q0
  have eq : 959 / 1024 * (q / 2 ^ 120) * (2 * (N - m)) = q * (959 / 512 * (N - m) / 2 ^ 120) := by ring
  linarith

theorem pinned_margin_243 (b q queries : ℕ) (wide : 243 ≤ b) (positive : 1 ≤ q)
    (small : q ≤ 2^120) (count : queries ≤ q + 2^31 + 4) :
    pinnedWidthTerm b queries ≤ (65 / 1024) * ((q : ℝ)/2^120) := by
  have qOne : (1 : ℝ) ≤ q := by exact_mod_cast positive
  have qUpper : (q : ℝ) ≤ 2^120 := by exact_mod_cast small
  have qNonneg : (0 : ℝ) ≤ q := by positivity
  have nonneg : (0 : ℝ) ≤ queries := by positivity
  have terms : (queries : ℝ) ≤ (q : ℝ) + 2^31 + 4 := by exact_mod_cast count
  have queriesUpper : (queries : ℝ) ≤ 2^121 := by
    have threshold : (2 : ℝ)^120 + 2^31 + 4 ≤ 2^121 := by norm_num
    linarith
  have denominator : (2 : ℝ)^1600 - 2^121 ≤ 2^1600-(queries : ℝ) := by linarith
  have denominatorPos : (0 : ℝ) < 2^1600-(queries : ℝ) := by
    have : (0 : ℝ) < 2^1600 - 2^121 := by norm_num
    linarith
  have fiber : (2 : ℝ)^(1600-b) ≤ 2^1357 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have squareBound : (queries : ℝ)^2 ≤ (q : ℝ)*(2^120 + 2^65) := by
    let extra : ℝ := 2^31+4
    have leSum : (queries : ℝ) ≤ q + extra := by linarith [show extra = (2:ℝ)^31+4 from rfl]
    have sq := mul_le_mul leSum leSum nonneg (by positivity)
    have qsq := mul_le_mul_of_nonneg_right qUpper qNonneg
    have esq : 2*extra*q + extra^2 ≤ q*2^65 := by
      have e1 : 2*extra ≤ 2^33 := by norm_num [extra]
      have e2 : extra^2 ≤ 2^64 := by norm_num [extra]
      nlinarith
    nlinarith
  have linearBound : (queries : ℝ) ≤ (q : ℝ)*2^33 := by
    have extra : (2 : ℝ)^31 + 4 ≤ 2^32 := by norm_num
    nlinarith
  have kBound : (2 : ℝ)^(1600-b) + 2^1345 + 2^897 ≤ 2^1357 + 2^1345 + 2^897 := by linarith
  have pairs : ((queries : ℝ) * ((queries : ℝ)-1)/2) * (2^(1600-b) + 2^1345 + 2^897) ≤
      (queries : ℝ)^2 / 2 * (2^1357 + 2^1345 + 2^897) := by
    have k0 : (0 : ℝ) ≤ 2^(1600-b) + 2^1345 + 2^897 := by positivity
    have : (queries : ℝ) * ((queries : ℝ) - 1) / 2 ≤ (queries : ℝ)^2 / 2 := by nlinarith
    calc _ ≤ (queries : ℝ)^2 / 2 * (2^(1600-b) + 2^1345 + 2^897) := mul_le_mul_of_nonneg_right this k0
      _ ≤ _ := mul_le_mul_of_nonneg_left kBound (by positivity)
  have total : ((queries : ℝ) * ((queries : ℝ)-1)/2) * (2^(1600-b) + 2^1345 + 2^897) + (queries : ℝ)*2^896 ≤
      (q : ℝ) * ((2^120 + 2^65) * (2^1357 + 2^1345 + 2^897) / 2 + 2^929) := by
    have a := mul_le_mul_of_nonneg_right squareBound (by positivity : (0 : ℝ) ≤ (2^1357 + 2^1345 + 2^897)/2)
    have c := mul_le_mul_of_nonneg_right linearBound (by positivity : (0 : ℝ) ≤ 2^896)
    nlinarith
  have constant : (2^120 + 2^65 : ℝ) * (2^1357 + 2^1345 + 2^897) / 2 + 2^929 ≤ 65 / 1024 / 2^120 * (2^1600 - 2^121) := by
    norm_num
  unfold pinnedWidthTerm
  rw [div_le_iff₀ denominatorPos]
  have scaled := mul_le_mul_of_nonneg_left constant qNonneg
  have den := mul_le_mul_of_nonneg_left denominator (by positivity : (0 : ℝ) ≤ (65 / 1024) * ((q : ℝ)/2^120))
  have eq : (q : ℝ) * (65 / 1024 / 2^120 * (2^1600 - 2^121)) = (65 / 1024) * ((q : ℝ)/2^120) * (2^1600 - 2^121) := by ring
  linarith

theorem internal_margin_243 (q m : ℕ) (positive : 1 ≤ q) (small : q ≤ 2^120)
    (hm : m ≤ q+2^31) :
    1-Real.exp (-collisionExponent (2^238) m) ≤ (959/1024)*((q : ℝ)/2^120) := by
  have q1 : (1 : ℝ) ≤ q := by exact_mod_cast positive
  have qs : (q : ℝ) ≤ 2^120 := by exact_mod_cast small
  have mR : (m : ℝ) ≤ q+2^31 := by exact_mod_cast hm
  have m0 : (0 : ℝ) ≤ m := by positivity
  have N : (2 : ℝ)^238 ≤ 2^238 := le_rfl
  have piece : ∀ lo hi u : ℝ, lo*2^120 ≤ q → q ≤ hi*2^120 → 1/4 ≤ hi → hi ≤ 1 →
      2^239/2^238*hi^2*(1001/1000) ≤ u → u ≤ ((64 : ℕ) : ℝ) →
      1-(1-u/((64 : ℕ) : ℝ))^64 ≤ (959/1024)*lo →
      1-Real.exp (-collisionExponent (2^238) m) ≤ (959/1024)*((q : ℝ)/2^120) := by
    intro lo hi u hl hh h4 h1 hu hu64 check
    exact interval_step _ _ _ lo u 64
      ((exponent_le _ _ _ hi N hh mR m0 (by linarith) h4 h1).trans hu) hu64 (by norm_num)
      (by rw [le_div_iff₀ (by positivity)];linarith) (by norm_num) check
  by_cases h0 : (q : ℝ) ≤ (2/5)*2^120
  · exact small_budget_243 _ _ _ (2/5) N q1 h0 mR m0 (by norm_num) (by norm_num)
  by_cases h21 : (q : ℝ) ≤ (21/50)*2^120
  · exact piece (20/50) (21/50) (441441/1250000) (by linarith) h21 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h21 := le_of_lt (not_le.mp h21)
  by_cases h22 : (q : ℝ) ≤ (22/50)*2^120
  · exact piece (21/50) (22/50) (484484/1250000) (by linarith) h22 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h22 := le_of_lt (not_le.mp h22)
  by_cases h23 : (q : ℝ) ≤ (23/50)*2^120
  · exact piece (22/50) (23/50) (529529/1250000) (by linarith) h23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h23 := le_of_lt (not_le.mp h23)
  by_cases h24 : (q : ℝ) ≤ (24/50)*2^120
  · exact piece (23/50) (24/50) (576576/1250000) (by linarith) h24 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h24 := le_of_lt (not_le.mp h24)
  by_cases h25 : (q : ℝ) ≤ (25/50)*2^120
  · exact piece (24/50) (25/50) (625625/1250000) (by linarith) h25 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h25 := le_of_lt (not_le.mp h25)
  by_cases h26 : (q : ℝ) ≤ (26/50)*2^120
  · exact piece (25/50) (26/50) (676676/1250000) (by linarith) h26 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h26 := le_of_lt (not_le.mp h26)
  by_cases h27 : (q : ℝ) ≤ (27/50)*2^120
  · exact piece (26/50) (27/50) (729729/1250000) (by linarith) h27 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h27 := le_of_lt (not_le.mp h27)
  by_cases h28 : (q : ℝ) ≤ (28/50)*2^120
  · exact piece (27/50) (28/50) (784784/1250000) (by linarith) h28 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h28 := le_of_lt (not_le.mp h28)
  by_cases h29 : (q : ℝ) ≤ (29/50)*2^120
  · exact piece (28/50) (29/50) (841841/1250000) (by linarith) h29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h29 := le_of_lt (not_le.mp h29)
  by_cases h30 : (q : ℝ) ≤ (30/50)*2^120
  · exact piece (29/50) (30/50) (900900/1250000) (by linarith) h30 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h30 := le_of_lt (not_le.mp h30)
  by_cases h31 : (q : ℝ) ≤ (31/50)*2^120
  · exact piece (30/50) (31/50) (961961/1250000) (by linarith) h31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h31 := le_of_lt (not_le.mp h31)
  by_cases h32 : (q : ℝ) ≤ (32/50)*2^120
  · exact piece (31/50) (32/50) (1025024/1250000) (by linarith) h32 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h32 := le_of_lt (not_le.mp h32)
  by_cases h33 : (q : ℝ) ≤ (33/50)*2^120
  · exact piece (32/50) (33/50) (1090089/1250000) (by linarith) h33 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h33 := le_of_lt (not_le.mp h33)
  by_cases h34 : (q : ℝ) ≤ (34/50)*2^120
  · exact piece (33/50) (34/50) (1157156/1250000) (by linarith) h34 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h34 := le_of_lt (not_le.mp h34)
  by_cases h35 : (q : ℝ) ≤ (35/50)*2^120
  · exact piece (34/50) (35/50) (1226225/1250000) (by linarith) h35 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h35 := le_of_lt (not_le.mp h35)
  by_cases h36 : (q : ℝ) ≤ (36/50)*2^120
  · exact piece (35/50) (36/50) (1297296/1250000) (by linarith) h36 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h36 := le_of_lt (not_le.mp h36)
  by_cases h37 : (q : ℝ) ≤ (37/50)*2^120
  · exact piece (36/50) (37/50) (1370369/1250000) (by linarith) h37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h37 := le_of_lt (not_le.mp h37)
  by_cases h38 : (q : ℝ) ≤ (38/50)*2^120
  · exact piece (37/50) (38/50) (1445444/1250000) (by linarith) h38 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h38 := le_of_lt (not_le.mp h38)
  by_cases h39 : (q : ℝ) ≤ (39/50)*2^120
  · exact piece (38/50) (39/50) (1522521/1250000) (by linarith) h39 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h39 := le_of_lt (not_le.mp h39)
  by_cases h40 : (q : ℝ) ≤ (40/50)*2^120
  · exact piece (39/50) (40/50) (1601600/1250000) (by linarith) h40 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h40 := le_of_lt (not_le.mp h40)
  by_cases h41 : (q : ℝ) ≤ (41/50)*2^120
  · exact piece (40/50) (41/50) (1682681/1250000) (by linarith) h41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h41 := le_of_lt (not_le.mp h41)
  by_cases h42 : (q : ℝ) ≤ (42/50)*2^120
  · exact piece (41/50) (42/50) (1765764/1250000) (by linarith) h42 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h42 := le_of_lt (not_le.mp h42)
  by_cases h43 : (q : ℝ) ≤ (43/50)*2^120
  · exact piece (42/50) (43/50) (1850849/1250000) (by linarith) h43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h43 := le_of_lt (not_le.mp h43)
  by_cases h44 : (q : ℝ) ≤ (44/50)*2^120
  · exact piece (43/50) (44/50) (1937936/1250000) (by linarith) h44 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h44 := le_of_lt (not_le.mp h44)
  by_cases h45 : (q : ℝ) ≤ (45/50)*2^120
  · exact piece (44/50) (45/50) (2027025/1250000) (by linarith) h45 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h45 := le_of_lt (not_le.mp h45)
  by_cases h46 : (q : ℝ) ≤ (46/50)*2^120
  · exact piece (45/50) (46/50) (2118116/1250000) (by linarith) h46 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h46 := le_of_lt (not_le.mp h46)
  by_cases h47 : (q : ℝ) ≤ (47/50)*2^120
  · exact piece (46/50) (47/50) (2211209/1250000) (by linarith) h47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h47 := le_of_lt (not_le.mp h47)
  by_cases h48 : (q : ℝ) ≤ (48/50)*2^120
  · exact piece (47/50) (48/50) (2306304/1250000) (by linarith) h48 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h48 := le_of_lt (not_le.mp h48)
  by_cases h49 : (q : ℝ) ≤ (49/50)*2^120
  · exact piece (48/50) (49/50) (2403401/1250000) (by linarith) h49 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  replace h49 := le_of_lt (not_le.mp h49)
  exact piece (49/50) (50/50) (2502500/1250000) (by linarith) (by simpa using qs) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem combined_margin_243 (q m n : ℕ) (positive : 1 ≤ q) (small : q ≤ 2^120)
    (hm : m ≤ q+2^31) (hn : n ≤ q+2^31+4) :
    1-Real.exp (-collisionExponent (2^238) m)+pinnedWidthTerm 243 n ≤ (q : ℝ)/2^120 := by
  have a := internal_margin_243 q m positive small hm
  have b := pinned_margin_243 243 q n (by decide) positive small hn
  linarith

theorem combined_margin_243_capped (q m n : ℕ) (positive : 1 ≤ q)
    (hm : m ≤ q+2^31) (hn : n ≤ q+2^31+4) :
    min 1 (1-Real.exp (-collisionExponent (2^238) m)+pinnedWidthTerm 243 n) ≤ (q : ℝ)/2^120 := by
  by_cases small : q ≤ 2^120
  · exact (min_le_right _ _).trans (combined_margin_243 q m n positive small hm hn)
  · have upper : (2 : ℝ)^120 ≤ q := by exact_mod_cast (Nat.le_of_lt (Nat.not_le.mp small))
    exact (min_le_left _ _).trans ((le_div_iff₀ (by positivity)).mpr (by linarith))

end TwoPermutationPrototype.Sampling
