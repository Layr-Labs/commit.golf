import CommitGolfCandidate.JointOracleHazardArithmetic

/-! Conditional hazards for the oracle actually queried in the joint lazy run. -/

namespace CommitGolfCandidate.JointOracle
open CommitGolf OracleComp OracleSpec Permutation TwoPermutationPrototype.Sampling
set_option exponentiation.threshold 2100
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

theorem fresh_hazard (query : PublicSpec.Domain) (s : State) (known : Nat)
    (bounded : s.count ≤ known) (safe : ¬ bad s) :
    Pr{let result ← (handler (.inr query)).run s}[bad result.2] ≤
      ((known+1 : Nat) : ENNReal)/2^238 := by
  classical
  by_cases high : 2^238 ≤ known+1
  · refine (prEvent_le_one _).trans ?_
    calc
      (1 : ENNReal) = (2^238 : ENNReal)/2^238 :=
        (ENNReal.div_self (by norm_num) (by norm_num)).symm
      _ ≤ ((known+1 : Nat) : ENNReal)/2^238 :=
        ENNReal.div_le_div_right (by exact_mod_cast high) _
  have small : known < 2^238 := by omega
  have cacheSafe : ¬ ProjectedCollisionW 238 s.cache := fun h => safe (Or.inl h)
  have good : (s3PinCallW 242).badSpec.Good s.trace :=
    not_not.mp fun h => safe (Or.inr h)
  have traceBound : s.trace.length ≤ known := by have := s.size; omega
  rcases query with input | input | output
  · change prEvent ((fun result => bad result.2) <$>
      (match s.cache input with
       | some answer => pure (answer,s.bump)
       | none => do let answer ← $ᵗ CompressionSpec.Range input; pure (answer,s.store input answer))) ≤ _
    split
    · rw [prEvent_pure]
      have bumped : ¬ bad s.bump := safe
      simp only [bumped,ite_false]
      exact zero_le
    · rw [bind_pure_comp,Functor.map_map]
      change Pr{let answer ← $ᵗ CompressionSpec.Range input}[bad (s.store input answer)] ≤ _
      simp only [bad,State.store,good,not_true_eq_false,or_false]
      refine (fresh_projected_collision_bound_w 238 (by decide) s.cache input s.keys cacheSafe s.covers).trans ?_
      apply ENNReal.div_le_div_right
      exact_mod_cast (show s.keys.card ≤ known+1 by have := s.size; omega)
  · change prEvent ((fun result => bad result.2) <$>
      (do let answer ← sampleSet (s.trace.fwdAns input) (s.wf.fwdAns_nonempty input)
          pure (answer.val,s.forward input answer.val answer.property))) ≤ _
    rw [bind_pure_comp,Functor.map_map]
    change Pr{let answer ← sampleSet (s.trace.fwdAns input) (s.wf.fwdAns_nonempty input)}[
      bad (s.forward input answer.val answer.property)] ≤ _
    simp only [bad,State.forward,cacheSafe,false_or]
    by_cases cached : input ∈ s.trace.usedIn
    · simp only [Trace.stepF,cached,ite_true,good,not_true_eq_false,prEvent_false]
      exact zero_le
    · have count := pinned242_forward_card s.trace good input (s.trace.fwdAns input)
      have countN : ((s.trace.fwdAns input).filter fun y =>
          ¬ (s3PinCallW 242).badSpec.Good (s.trace.stepF input y)).card ≤ s.trace.length*2^1359+2^896 := by
        exact count.trans (Nat.le_add_right _ _)
      have sample := sampleSet_bound (s.trace.fwdAns input) (s.wf.fwdAns_nonempty input)
        (fun y => ¬ (s3PinCallW 242).badSpec.Good (s.trace.stepF input y)) _ countN
      have card : (s.trace.fwdAns input).card = 2^1600-s.trace.length := by
        rw [Trace.fwdAns,ite_eq_right (fun h => (cached h).elim),s.wf.card_freeOut]
        rw [← FinEnum.card_eq_fintypeCard,FinEnum.card_bitVec]
        rfl
      rw [card] at sample
      exact sample.trans (permutation_hazard s.trace.length known traceBound small)
  · change prEvent ((fun result => bad result.2) <$>
      (do let answer ← sampleSet (s.trace.invAns output) (s.wf.invAns_nonempty output)
          pure (answer.val,s.inverse answer.val output answer.property))) ≤ _
    rw [bind_pure_comp,Functor.map_map]
    change Pr{let answer ← sampleSet (s.trace.invAns output) (s.wf.invAns_nonempty output)}[
      bad (s.inverse answer.val output answer.property)] ≤ _
    simp only [bad,State.inverse,cacheSafe,false_or]
    by_cases cached : output ∈ s.trace.usedOut
    · simp only [Trace.stepI,cached,ite_true,good,not_true_eq_false,prEvent_false]
      exact zero_le
    · have count := pinned242_inverse_card s.trace good output (s.trace.invAns output)
      have countN : ((s.trace.invAns output).filter fun x =>
          ¬ (s3PinCallW 242).badSpec.Good (s.trace.stepI x output)).card ≤
          s.trace.length*2^1359+2^896 := count
      have sample := sampleSet_bound (s.trace.invAns output) (s.wf.invAns_nonempty output)
        (fun x => ¬ (s3PinCallW 242).badSpec.Good (s.trace.stepI x output)) _ countN
      have card : (s.trace.invAns output).card = 2^1600-s.trace.length := by
        rw [Trace.invAns,ite_eq_right (fun h => (cached h).elim),s.wf.card_freeIn]
        rw [← FinEnum.card_eq_fintypeCard,FinEnum.card_bitVec]
        rfl
      rw [card] at sample
      exact sample.trans (permutation_hazard s.trace.length known traceBound small)

noncomputable def model : JointOracleBudget State where
  handler := handler
  valid s known := s.count ≤ known
  bad := bad
  coins := handler_coins
  preserves query s known bounded result reached := by
    rw [handler_count query s result reached]
    omega
  fresh := fresh_hazard

theorem empty_safe : ¬ bad State.empty := by
  rintro (collision | permutation)
  · obtain ⟨_,_,_,_,_,missing,_⟩ := collision
    contradiction
  · exact permutation ((s3PinCallW 242).badSpec.good_nil)

/-- Every actual public query consumes one common survival factor. -/
theorem joint_survival {α : Type} (program : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound program budget) :
    Pr{let result ← model.run program State.empty}[bad result.2] ≤
      1-survival 238 1 budget :=
  model.adaptive_survival program budget 0 bounded State.empty (Nat.le_refl 0) empty_safe

end CommitGolfCandidate.JointOracle
