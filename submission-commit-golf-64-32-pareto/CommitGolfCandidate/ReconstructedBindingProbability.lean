import CommitGolfCandidate.ReconstructedBindingPermutation

namespace CommitGolfCandidate.Reconstruction.Binding
open CommitGolf OracleComp OracleSpec CommitGolfCandidate.JointOracle241
set_option exponentiation.threshold 2100
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

private theorem empty_good : Good State.empty := by
  have no {seed : Seed} {v : Digest} : finish (table State.empty) seed ≠ some v := by
    intro run
    obtain ⟨k,_,read⟩ := Option.bind_eq_some_iff.1 run
    change none = some v at read
    cases read
  refine ⟨?_,?_,(TwoPermutationPrototype.Sampling.s3PinCallW 240).badSpec.good_nil⟩
  · intro a b v h _; change none = some v at h; cases h
  · rintro ⟨_,_,_,_,_,_,l,_,_⟩; exact no l

private noncomputable def query_step (query : PublicSpec.Domain) (s : State) (good : Good s)
    (small : s.count < 2^238) : StepBound query s :=
  match query with
  | .inl k => compression_step k s good
  | .inr (.inl k) => forward_step k s good small
  | .inr (.inr k) => inverse_step k s good small

private theorem query_charge (Q : Nat) (small : Q ≤ 2^121)
    (query : PublicSpec.Domain) (s : State) (room : s.count < Q) (good : Good s) :
    ∃ (reject : PublicSpec.Range query × State → Prop) (delta : ℝ),
      0 ≤ delta ∧ credit (used s) s.count + delta ≤ cap Q ∧
      Pr{let r ← handler (.inr query) s}[reject r] ≤ 1-ENNReal.ofReal (Real.exp (-delta)) ∧
      ∀ r ∈ support (handler (.inr query) s), ¬ reject r → Good r.2 ∧
        credit (used s) s.count + delta ≤ credit (used r.2) r.2.count := by
  let b := query_step query s good (by omega)
  have bu := used_le s good
  have bw := b.bound
  have d0 := increment_nonneg (n := (used s : ℝ)) (c := (s.count : ℝ)) (w := (b.w : ℝ))
    (by positivity) (by positivity) (by positivity)
  refine ⟨b.reject,increment (used s) s.count b.w,d0,?_,?_,?_⟩
  · unfold increment
    rw [add_sub_cancel]
    apply credit_mono (by positivity) (by positivity)
    · exact_mod_cast (show used s+b.w ≤ Q+9 by omega)
    · exact_mod_cast (show s.count+1 ≤ Q+1 by omega)
  · have rate := hazard_le_loss (n := (used s : ℝ)) (c := (s.count : ℝ)) (w := (b.w : ℝ))
        (by positivity) (by positivity) (by positivity)
        (by exact_mod_cast (show used s ≤ 2^121 by omega))
        (by exact_mod_cast (show s.count ≤ 2^121 by omega)) (by exact_mod_cast bw)
    have scale := ENNReal.ofReal_le_ofReal rate
    rw [ENNReal.ofReal_sub _ (Real.exp_pos _).le,ENNReal.ofReal_one] at scale
    exact b.rate.trans scale
  · intro r hr ok
    obtain ⟨yes,hu⟩ := b.live r hr ok
    have hc := handler_count query s r hr
    refine ⟨yes,?_⟩
    unfold increment
    rw [hu,hc,add_sub_cancel]
    push_cast
    exact le_rfl

theorem lazy_replay_bound {α : Type} (program : OracleComp World α) (q Q : Nat) (positive : 1 ≤ q)
    (replayed : Q ≤ q+2^32) (bounded : PublicQueryBound program Q) :
    Pr{let r ← model.run program State.empty}[¬ Good r.2] ≤ (q:ENNReal)/2^120 := by
  by_cases hi : 2^120 ≤ q
  · refine (prEvent_le_one _).trans ?_
    calc
      (1:ENNReal) = (2^120:ENNReal)/2^120 := (ENNReal.div_self (by norm_num) (by norm_num)).symm
      _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast hi) _
  have small : q < 2^120 := by omega
  have bound := adaptive_exponential Good (fun s => credit (used s) s.count) (cap Q) Q
    (query_charge Q (by omega)) program Q bounded State.empty (by change 0+Q ≤ Q; omega) empty_good
  have e : ENNReal.ofReal (Real.exp (-cap Q)) ≤
      ENNReal.ofReal (Real.exp (credit (used State.empty) State.empty.count-cap Q)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [credit_nonneg (used State.empty) State.empty.count]))
  have margin := ENNReal.ofReal_le_ofReal (cap_margin q Q positive small replayed)
  rw [ENNReal.ofReal_sub _ (Real.exp_pos _).le,ENNReal.ofReal_one,
      ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < 2^120),ENNReal.ofReal_natCast] at margin
  have two : ENNReal.ofReal ((2:ℝ)^120) = (2:ENNReal)^120 := by norm_num
  rw [two] at margin
  exact bound.trans ((tsub_le_tsub_left e _).trans margin)

end CommitGolfCandidate.Reconstruction.Binding
