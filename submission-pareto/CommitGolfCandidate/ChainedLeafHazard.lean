import CommitGolfCandidate.JointOracle238HazardArithmetic

/-! Leaf hazards charged only to permutation queries, in either direction. -/
namespace CommitGolfCandidate.Chained
open CommitGolf OracleComp OracleSpec Permutation TwoPermutationPrototype.Sampling JointOracle238
set_option exponentiation.threshold 2100

private theorem high_rank (p : Nat) (high : 2^238 ≤ p+1) :
    (1 : ENNReal) ≤ ((p+1 : Nat) : ENNReal)/2^238 := by
  calc
    _ = (2^238 : ENNReal)/2^238 := (ENNReal.div_self (by norm_num) (by norm_num)).symm
    _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast high) _

theorem leaf_forward_hazard (trace : Permutation.Trace PermState) (wf : trace.WF)
    (good : (s3PinCallW 238).badSpec.Good trace) (p : Nat) (bounded : trace.length ≤ p) (input : PermState) :
    Pr{let answer ← sampleSet (trace.fwdAns input) (wf.fwdAns_nonempty input)}[
      ¬ (s3PinCallW 238).badSpec.Good (trace.stepF input answer.val)] ≤
      ((p+1 : Nat) : ENNReal)/2^238 := by
  classical
  by_cases high : 2^238 ≤ p+1
  · exact (prEvent_le_one _).trans (high_rank p high)
  have small : p < 2^238 := by omega
  by_cases cached : input ∈ trace.usedIn
  · simp only [Trace.stepF,cached,ite_true,good,not_true_eq_false,prEvent_false]
    exact zero_le
  · have count := pinned238_forward_card trace good input (trace.fwdAns input)
    have countN : ((trace.fwdAns input).filter fun y =>
        ¬ (s3PinCallW 238).badSpec.Good (trace.stepF input y)).card ≤ trace.length*pairFiber238+2^896 :=
      count.trans (Nat.le_add_right _ _)
    have sample := sampleSet_bound (trace.fwdAns input) (wf.fwdAns_nonempty input)
      (fun y => ¬ (s3PinCallW 238).badSpec.Good (trace.stepF input y)) _ countN
    have card : (trace.fwdAns input).card = 2^1600-trace.length := by
      rw [Trace.fwdAns,ite_eq_right (fun h => (cached h).elim),wf.card_freeOut]
      rw [← FinEnum.card_eq_fintypeCard,FinEnum.card_bitVec]
      rfl
    rw [card] at sample
    exact sample.trans (permutation_hazard trace.length p bounded small)

theorem leaf_inverse_hazard (trace : Permutation.Trace PermState) (wf : trace.WF)
    (good : (s3PinCallW 238).badSpec.Good trace) (p : Nat) (bounded : trace.length ≤ p) (output : PermState) :
    Pr{let answer ← sampleSet (trace.invAns output) (wf.invAns_nonempty output)}[
      ¬ (s3PinCallW 238).badSpec.Good (trace.stepI answer.val output)] ≤
      ((p+1 : Nat) : ENNReal)/2^238 := by
  classical
  by_cases high : 2^238 ≤ p+1
  · exact (prEvent_le_one _).trans (high_rank p high)
  have small : p < 2^238 := by omega
  by_cases cached : output ∈ trace.usedOut
  · simp only [Trace.stepI,cached,ite_true,good,not_true_eq_false,prEvent_false]
    exact zero_le
  · have count := pinned238_inverse_card trace good output (trace.invAns output)
    have sample := sampleSet_bound (trace.invAns output) (wf.invAns_nonempty output)
      (fun x => ¬ (s3PinCallW 238).badSpec.Good (trace.stepI x output)) _ count
    have card : (trace.invAns output).card = 2^1600-trace.length := by
      rw [Trace.invAns,ite_eq_right (fun h => (cached h).elim),wf.card_freeIn]
      rw [← FinEnum.card_eq_fintypeCard,FinEnum.card_bitVec]
      rfl
    rw [card] at sample
    exact sample.trans (permutation_hazard trace.length p bounded small)

end CommitGolfCandidate.Chained
