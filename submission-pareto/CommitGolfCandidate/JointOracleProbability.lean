import CommitGolfCandidate.JointOracleHazards
import CommitGolfCandidate.Leaf242JointMargin

namespace CommitGolfCandidate.JointOracle
open CommitGolf OracleComp TwoPermutationPrototype.Sampling
set_option exponentiation.threshold 2100
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem lazy_bad_target {α : Type} (program : OracleComp World α) (q calls : Nat)
    (positive : 1 ≤ q) (replay : calls ≤ q+2^31)
    (bounded : PublicQueryBound program calls) :
    Pr{let result ← model.run program State.empty}[bad result.2] ≤ (q : ENNReal)/2^120 := by
  by_cases large : 2^120 ≤ q
  · refine (prEvent_le_one _).trans ?_
    calc
      (1 : ENNReal) = (2^120 : ENNReal)/2^120 :=
        (ENNReal.div_self (by norm_num) (by norm_num)).symm
      _ ≤ (q : ENNReal)/2^120 :=
        ENNReal.div_le_div_right (by exact_mod_cast large) _
  have small : q < 2^120 := by omega
  have shift : survival 238 0 (calls+1) = survival 238 1 calls := by
    rw [survival_succ]
    norm_num
  refine (joint_survival program calls bounded).trans ?_
  rw [← shift]
  calc
    1-survival 238 0 (calls+1) ≤
        1-ENNReal.ofReal (Real.exp (-collisionExponent (2^238) (calls+1))) :=
      by simpa only [Nat.cast_add,Nat.cast_one] using
        tsub_le_tsub_left (survival_ge_exp 238 (calls+1) (by omega)) 1
    _ = ENNReal.ofReal (1-Real.exp (-collisionExponent (2^238) (calls+1))) := by
      rw [ENNReal.ofReal_sub _ (Real.exp_pos _).le,ENNReal.ofReal_one]
    _ ≤ (q : ENNReal)/2^120 := by
      have bound := ENNReal.ofReal_le_ofReal (joint_margin_242 q calls positive small replay)
      simpa only [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2^120),
        ENNReal.ofReal_natCast,
        show ENNReal.ofReal ((2 : ℝ)^120) = (2 : ENNReal)^120 from by norm_num] using bound

end CommitGolfCandidate.JointOracle
