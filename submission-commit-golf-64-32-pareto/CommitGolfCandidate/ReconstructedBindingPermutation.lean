import CommitGolfCandidate.ReconstructedBindingCompression
import CommitGolfCandidate.PinCallNatCounts

namespace CommitGolfCandidate.Reconstruction.Binding
open CommitGolf OracleComp OracleSpec CommitGolfCandidate.JointOracle241
open CommitGolfCandidate.Permutation TwoPermutationPrototype.Sampling Finset
set_option exponentiation.threshold 2100
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable
private abbrev H := s3PinCallW 240

private theorem pin_fibers :
    (∀ x old, ∃ F : Finset S3State, F.card ≤ 2^1361 ∧
      ∀ y, H.badSpec.pair ⟨.fwd,x,y⟩ old → y ∈ F) ∧
    (∀ x y, ¬ H.badSpec.single ⟨.fwd,x,y⟩) ∧
    (∀ y old, ∃ F : Finset S3State, F.card ≤ 2^1361 ∧
      ∀ x, H.badSpec.pair ⟨.inv,x,y⟩ old → x ∈ F) ∧
    (∀ y, ∃ F : Finset S3State, F.card ≤ 2^896 ∧
      ∀ x, H.badSpec.single ⟨.inv,x,y⟩ → x ∈ F) :=
  PinCall.answer_fibers H (2^1360) (2^896) (2^1344) (2^896) (2^1361)
  (by intro d; simpa only [Nat.reduceSub] using s3_trunc_width_fiber 240 (by decide) d)
  s3_chop_fiber s3_pin_fiber (by norm_num) (by norm_num) (by norm_num)

private theorem permutation_rate (r known : Nat) (bounded : r ≤ known) (small : known < 2^238) :
    ((r*2^1361+2^896 : Nat) : ENNReal)/((2^1600-r : Nat) : ENNReal) ≤
      ((known+1 : Nat) : ENNReal)/2^238 := by
  have rSmall : r ≤ 2^238 := by omega
  have rCard : r ≤ 2^1600 := by omega
  have denominator : (0 : ℝ) < ((2^1600-r : Nat) : ℝ) := by
    exact_mod_cast (show 0 < 2^1600-r by omega)
  have rate : ((r*2^1361+2^896 : Nat) : ℝ)/((2^1600-r : Nat) : ℝ) ≤
      ((known+1 : Nat) : ℝ)/2^238 := by
    rw [div_le_iff₀ denominator]
    rw [Nat.cast_sub rCard]
    push_cast
    have rr : (r : ℝ) ≤ known := by exact_mod_cast bounded
    have rs : (r : ℝ) ≤ 2^238 := by exact_mod_cast rSmall
    have half : (2^1599 : ℝ) ≤ 2^1600-r := by nlinarith
    have scale : (2^1361 : ℝ) ≤ 2^1599/2^238 := by norm_num
    have unary : (2^896 : ℝ) ≤ 2^1361 := by norm_num
    have calculation : (r : ℝ)*2^1361+2^896 ≤ ((known : ℝ)+1)/2^238*(2^1600-r) := by
      calc
        (r : ℝ)*2^1361+2^896 ≤ ((known : ℝ)+1)*2^1361 := by nlinarith
        _ ≤ ((known : ℝ)+1)*(2^1599/2^238) := by gcongr
        _ ≤ ((known : ℝ)+1)*((2^1600-r)/2^238) := by gcongr
        _ = ((known : ℝ)+1)/2^238*(2^1600-r) := by ring
    norm_num only at calculation ⊢
    exact calculation
  have converted := ENNReal.ofReal_le_ofReal rate
  simpa only [ENNReal.ofReal_div_of_pos denominator,
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2^238),
    ENNReal.ofReal_natCast,
    show ENNReal.ofReal ((2 : ℝ)^238) = (2 : ENNReal)^238 from by norm_num] using converted


private theorem rate_to_hazard (s : State) :
    ((used s+1 : Nat) : ENNReal)/2^238 ≤ ENNReal.ofReal (hazard (used s) s.count 1) := by
  have r := ENNReal.ofReal_le_ofReal (show ((used s+1 : Nat) : ℝ)/2^238 ≤ hazard (used s) s.count 1 from by
    unfold hazard
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) (used s), Nat.cast_nonneg (α := ℝ) s.count])
  simpa only [ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ)<2^238),
    ENNReal.ofReal_natCast,show ENNReal.ofReal ((2:ℝ)^238) = (2:ENNReal)^238 by norm_num] using r

noncomputable def forward_step (k : PermState) (s : State) (good : Good s) (small : s.count < 2^238) :
    StepBound (.inr (.inl k)) s := by
  classical
  refine ⟨if k ∈ s.trace.usedIn then 0 else 1,by split <;> decide,fun r => ¬ H.badSpec.Good r.2.trace,?_,?_⟩
  · change prEvent ((fun r => ¬ H.badSpec.Good r.2.trace) <$>
      (do let a ← sampleSet (s.trace.fwdAns k) (s.wf.fwdAns_nonempty k)
          pure (a.val,s.forward k a.val a.property))) ≤ _
    rw [bind_pure_comp,Functor.map_map]
    change Pr{let a ← sampleSet (s.trace.fwdAns k) (s.wf.fwdAns_nonempty k)}[
      ¬ H.badSpec.Good (s.trace.stepF k a.val)] ≤ _
    by_cases cached : k ∈ s.trace.usedIn
    · simp only [Trace.stepF,cached,ite_true,good.2.2,not_true_eq_false,prEvent_false]
      exact zero_le
    · have count : ((s.trace.fwdAns k).filter fun v => ¬ H.badSpec.Good (s.trace.stepF k v)).card
          ≤ s.trace.length * 2^1361 + 2^896 := by
        let c := forward_bad_card H.badSpec (2^1361) pin_fibers.1 pin_fibers.2.1 s.trace good.2.2 k (s.trace.fwdAns k)
        exact c.trans (Nat.le_add_right _ _)
      have sample := sampleSet_bound (s.trace.fwdAns k) (s.wf.fwdAns_nonempty k)
        (fun v => ¬ H.badSpec.Good (s.trace.stepF k v)) _ count
      have card : (s.trace.fwdAns k).card = 2^1600-s.trace.length := by
        rw [Trace.fwdAns,ite_eq_right (fun h => (cached h).elim),s.wf.card_freeOut]
        rw [← FinEnum.card_eq_fintypeCard,FinEnum.card_bitVec]
        rfl
      rw [card] at sample
      simp only [cached,ite_false,Nat.cast_one]
      exact sample.trans ((permutation_rate _ _ (by unfold Reconstruction.Binding.used; omega)
        (lt_of_le_of_lt (used_le s good) small)).trans (rate_to_hazard s))
  · intro r hr live
    change r ∈ support (do
      let a ← sampleSet (s.trace.fwdAns k) (s.wf.fwdAns_nonempty k)
      pure (a.val,s.forward k a.val a.property)) at hr
    simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at hr
    obtain ⟨a,_,rfl⟩ := hr
    refine ⟨⟨good.1,good.2.1,not_not.mp live⟩,?_⟩
    change mass (table s) + (s.trace.stepF k a.val).length = _
    unfold Reconstruction.Binding.used
    by_cases cached : k ∈ s.trace.usedIn <;> simp [Trace.stepF,cached,List.length_cons] <;> omega

noncomputable def inverse_step (k : PermState) (s : State) (good : Good s) (small : s.count < 2^238) :
    StepBound (.inr (.inr k)) s := by
  classical
  refine ⟨if k ∈ s.trace.usedOut then 0 else 1,by split <;> decide,fun r => ¬ H.badSpec.Good r.2.trace,?_,?_⟩
  · change prEvent ((fun r => ¬ H.badSpec.Good r.2.trace) <$>
      (do let a ← sampleSet (s.trace.invAns k) (s.wf.invAns_nonempty k)
          pure (a.val,s.inverse a.val k a.property))) ≤ _
    rw [bind_pure_comp,Functor.map_map]
    change Pr{let a ← sampleSet (s.trace.invAns k) (s.wf.invAns_nonempty k)}[
      ¬ H.badSpec.Good (s.trace.stepI a.val k)] ≤ _
    by_cases cached : k ∈ s.trace.usedOut
    · simp only [Trace.stepI,cached,ite_true,good.2.2,not_true_eq_false,prEvent_false]
      exact zero_le
    · have count : ((s.trace.invAns k).filter fun v => ¬ H.badSpec.Good (s.trace.stepI v k)).card
          ≤ s.trace.length * 2^1361 + 2^896 := by
        exact inverse_bad_card H.badSpec (2^1361) (2^896) pin_fibers.2.2.1 pin_fibers.2.2.2
          s.trace good.2.2 k (s.trace.invAns k)
      have sample := sampleSet_bound (s.trace.invAns k) (s.wf.invAns_nonempty k)
        (fun v => ¬ H.badSpec.Good (s.trace.stepI v k)) _ count
      have card : (s.trace.invAns k).card = 2^1600-s.trace.length := by
        rw [Trace.invAns,ite_eq_right (fun h => (cached h).elim),s.wf.card_freeIn]
        rw [← FinEnum.card_eq_fintypeCard,FinEnum.card_bitVec]
        rfl
      rw [card] at sample
      simp only [cached,ite_false,Nat.cast_one]
      exact sample.trans ((permutation_rate _ _ (by unfold Reconstruction.Binding.used; omega)
        (lt_of_le_of_lt (used_le s good) small)).trans (rate_to_hazard s))
  · intro r hr live
    change r ∈ support (do
      let a ← sampleSet (s.trace.invAns k) (s.wf.invAns_nonempty k)
      pure (a.val,s.inverse a.val k a.property)) at hr
    simp only [support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at hr
    obtain ⟨a,_,rfl⟩ := hr
    refine ⟨⟨good.1,good.2.1,not_not.mp live⟩,?_⟩
    change mass (table s) + (s.trace.stepI a.val k).length = _
    unfold Reconstruction.Binding.used
    by_cases cached : k ∈ s.trace.usedOut <;> simp [Trace.stepI,cached,List.length_cons] <;> omega

end CommitGolfCandidate.Reconstruction.Binding
