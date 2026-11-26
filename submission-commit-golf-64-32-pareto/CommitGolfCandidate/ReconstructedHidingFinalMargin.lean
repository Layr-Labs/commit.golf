import CommitGolfCandidate.ReconstructedHidingGateCost

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf Generator HidingReplay HidingTraffic TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 2800000
set_option exponentiation.threshold 4096

private noncomputable def perPostExtra (n : Nat) : ℝ :=
  2*(n:ℝ)/2^1343 + (2*n+2*groupCount:ℝ)/((2:ℝ)^1600-2^122)

theorem joint_budget_margin (seen hidden opened q calls : Nat) (cached : seen≤calls)
    (used : calls≤q) (small : q+1≤2^120) (hiddenBound : hidden≤LENGTH) (openBound : opened≤LENGTH) :
    baseCost seen (2*LENGTH) + highCost opened + combinedPostError hidden (q-calls) +
      2*(restrictedError q+honestCost) ≤ ((q:ℝ)+1)/2^120 := by
  have fits : (q:ℝ) ≤ (2:ℝ)^120 := by exact_mod_cast (by omega : q≤2^120)
  have rem : ((q-calls:Nat):ℝ) ≤ (2:ℝ)^120 := by exact_mod_cast (by omega : q-calls≤2^120)
  have seenMax : (seen:ℝ) ≤ (2:ℝ)^120 := by exact_mod_cast (by omega : seen≤2^120)
  have members : ((q-calls:Nat):ℝ) + (seen:ℝ) ≤ q := by exact_mod_cast (by omega : q-calls+seen≤q)
  have pay : ((q-calls:Nat):ℝ)/2^120 + (seen:ℝ)/2^120 ≤ (q:ℝ)/2^120 := by
    rw [←add_div]
    exact div_le_div_of_nonneg_right members (by positivity)
  have hn : (hidden:ℝ)≤LENGTH := by exact_mod_cast hiddenBound
  have op : (opened:ℝ)≤LENGTH := by exact_mod_cast openBound
  have extrane : 0 ≤ perPostExtra hidden := by unfold perPostExtra; positivity
  have extraM : perPostExtra hidden ≤ perPostExtra LENGTH := by unfold perPostExtra; gcongr
  have extra := mul_le_mul rem extraM extrane (by positivity : (0:ℝ) ≤ 2^120)
  have closed : combinedPostError hidden (q-calls) = ((q-calls:Nat):ℝ)/2^120 + ((q-calls:Nat):ℝ)*perPostExtra hidden := by
    unfold combinedPostError rowRate perPostExtra
    ring
  have rest : restrictedError q ≤ (3*LENGTH:ℝ)*(((2:ℝ)^120+3*LENGTH)/2^1343) := by
    unfold restrictedError
    gcongr
  have old : baseCost seen (2*LENGTH) ≤ (seen:ℝ)/2^120 +
      (2:ℝ)^120*(groupCount/2^1600) + (2*LENGTH:ℝ)/2^192 +
      (groupCount:ℝ)*(2:ℝ)^120/2^360 + (groupCount:ℝ)*groupCount/2^1440 := by
    unfold baseCost
    push_cast
    rw [mul_add,mul_one_div]
    gcongr
  have hmax : highCost opened ≤ highCost LENGTH := by unfold highCost; gcongr
  have residual :
      (2:ℝ)^120*(groupCount/2^1600) + (2*LENGTH:ℝ)/2^192 + (groupCount:ℝ)*(2:ℝ)^120/2^360 +
      (groupCount:ℝ)*groupCount/2^1440 + highCost LENGTH + (2:ℝ)^120*perPostExtra LENGTH +
      2*((3*LENGTH:ℝ)*(((2:ℝ)^120+3*LENGTH)/2^1343)+honestCost) ≤ 1/2^120 := by
    norm_num [groupCount,LENGTH,LOG_LENGTH,highCost,perPostExtra,honestCost]
  rw [closed,add_div]
  linarith only [pay,extra,rest,old,hmax,residual]

end CommitGolfCandidate.Reconstruction.HidingTape
