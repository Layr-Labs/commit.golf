import CommitGolfCandidate.JointOracle238Completion

namespace CommitGolfCandidate.JointOracle238
open CommitGolf OracleComp OracleSpec Permutation
local instance {α : Type} : MeasurableSpace α := ⊤

theorem exp_ignore_count {S α : Type} [Fintype S] [DecidableEq S]
    (strategy : Strat S α) (trace : Trace S) (first second : Nat) (event : α → ℝ) :
    strategy.exp ⟨trace,first⟩ (fun value _ => event value) =
      strategy.exp ⟨trace,second⟩ (fun value _ => event value) := by
  induction strategy generalizing trace first second with
  | done value => rfl
  | fwd input next ih =>
    simp only [Strat.exp]
    exact avg_congr fun answer _ => ih answer _ _ _
  | inv output next ih =>
    simp only [Strat.exp]
    exact avg_congr fun answer _ => ih answer _ _ _
  | rand coins next ih =>
    simp only [Strat.exp]
    exact avg_congr fun answer _ => ih answer _ _ _

theorem sampleSet_bind_event {S α : Type} [Fintype S] (A : Finset S) (nonempty : A.Nonempty)
    (next : A → ProbComp α) (event : α → Prop) (value : S → ℝ)
    (nonneg : ∀ x, 0 ≤ value x)
    (equal : ∀ x, Pr{let result ← next x}[event result] = ENNReal.ofReal (value x.val)) :
    Pr{let result ← (sampleSet A nonempty >>= next)}[event result] =
      ENNReal.ofReal (avg A value) := by
  classical
  let : Nonempty A := ⟨⟨nonempty.choose,nonempty.choose_spec⟩⟩
  let : SampleableType A := SampleableType.ofFintype A
  change Pr{let result ← (($ᵗ A) >>= next)}[event result] = _
  rw [prEvent_bind_eq_sum_fintype]
  simp_rw [SampleableType.prEvent_uniformSample_eq_singleton,equal]
  rw [sum_inv_card_mul_ofReal (fun x : A => value x.val) (fun x => nonneg x.val)]
  congr 1
  simp only [avg,Finset.card_univ,Fintype.card_coe,Finset.sum_coe_sort]

theorem completed_probability (compression : Compression) {α : Type}
    (program : OracleComp World α) (event : α → Prop) (s : State) :
    Pr{let value ← completedOut compression program s}[event value] =
      ENNReal.ofReal ((toStrat compression program).exp ⟨s.trace,0⟩
        (fun value _ => ind (event value))) := by
  classical
  induction program using OracleComp.inductionOn generalizing s with
  | pure value =>
    simp only [completedOut_pure,to_strat_pure,Strat.exp,prEvent_pure,ofReal_ind]
  | query_bind query next ih =>
    rw [completedOut_query]
    rcases query with coins | input | input | output
    · rw [to_strat_coins]
      simp only [completedHandler,handler,bind_assoc,pure_bind,Strat.exp]
      rw [prEvent_bind_eq_sum_fintype]
      have mass : ∀ answer : Fin (coins+1),
          Pr{let drawn ← (liftM (unifSpec.query coins) : ProbComp (Fin (coins+1)))}[drawn=answer] =
            (Fintype.card (Fin (coins+1)) : ENNReal)⁻¹ := by
        intro answer
        have counted := prEvent_liftM_query_eq_card_div (spec := unifSpec) coins
          (fun drawn : Fin (coins+1) => drawn=answer)
        refine counted.trans ?_
        simp [Finset.filter_eq']
      rw [← sum_inv_card_mul_ofReal _ (fun answer =>
        Strat.exp_nonneg (fun _ _ => ind_nonneg _) _ _)]
      refine Finset.sum_congr rfl fun answer _ => ?_
      rw [mass answer,ih answer s]
    · rw [to_strat_compress]
      simp only [completedHandler]
      cases cached : s.cache input with
      | some answer =>
        simp only [pure_bind]
        exact ih (compression input) s.bump
      | none =>
        simp only [pure_bind]
        exact ih (compression input) (s.store input (compression input))
    · rw [to_strat_permute]
      simp only [completedHandler,handler,bind_assoc,pure_bind,Strat.exp]
      apply sampleSet_bind_event
      · intro answer
        exact Strat.exp_nonneg (fun _ _ => ind_nonneg _) _ _
      · intro answer
        rw [ih answer.val (s.forward input answer.val answer.property)]
        congr 1
        exact exp_ignore_count _ _ 0 1 _
    · rw [to_strat_inverse]
      simp only [completedHandler,handler,bind_assoc,pure_bind,Strat.exp]
      apply sampleSet_bind_event
      · intro answer
        exact Strat.exp_nonneg (fun _ _ => ind_nonneg _) _ _
      · intro answer
        rw [ih answer.val (s.inverse answer.val output answer.property)]
        congr 1
        exact exp_ignore_count _ _ 0 1 _

theorem joint_sampling_probability {α : Type} (program : OracleComp World α) (event : α → Prop) :
    Pr{let value ← (do
      let compression ← $ᵗ Compression
      let permutation ← $ᵗ Perm
      fixedOracleRun ⟨compression,permutation⟩ program)}[event value] =
      Pr{let value ← lazyOut program State.empty}[event value] := by
  have completion := (EvalDistEq.of_evalDist_eq (compression_completion program State.empty)).prEvent_eq event
  rw [completion]
  simp only [State.empty,tableExtending_empty]
  rw [prEvent_bind_eq_tsum]
  conv_rhs => rw [prEvent_bind_eq_tsum]
  apply tsum_congr
  intro compression
  rw [perm_sampling_prob,completed_probability]
  rfl

end CommitGolfCandidate.JointOracle238
