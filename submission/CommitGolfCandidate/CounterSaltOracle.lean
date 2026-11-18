import CommitGolfCandidate.CounterSaltLayout
import CommitGolfCandidate.NonceChainOracle

namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec Permutation Permutation.NonceChain
local instance counterDiscrete {α : Type} : MeasurableSpace α := ⊤
set_option linter.unusedSectionVars false
set_option maxRecDepth 12000
variable {α : Type}


noncomputable def counterNonceGame (c : Compression) (g : SaltArray → OracleComp World α) : ProbComp α := do
  let π ← $ᵗ Perm
  let k ← $ᵗ Key
  fixedOracleRun ⟨c,π⟩ (g (CounterSalt.salts π k))

private theorem uniform_mean {X : Type} [Fintype X] [SampleableType X]
    (f : X → ProbComp α) (event : α → Prop) :
    (prEvent (event <$> (($ᵗ X) >>= f))).toReal =
      mean (fun x => (prEvent (event <$> f x)).toReal) := by
  classical
  have ex : prEvent (event <$> (($ᵗ X) >>= f)) =
      ENNReal.ofReal (mean (fun x => (prEvent (event <$> f x)).toReal)) := by
    rw [prEvent_bind_eq_sum_fintype, ← sum_inv_card_mul_ofReal _ fun _ => ENNReal.toReal_nonneg]
    apply Finset.sum_congr rfl
    intro x _
    rw [SampleableType.prEvent_uniformSample_eq_singleton, ENNReal.ofReal_toReal (prEvent_ne_top _)]
  rw [ex, ENNReal.toReal_ofReal (avg_nonneg fun _ _ => ENNReal.toReal_nonneg)]

open Classical in
private noncomputable def eventStrategy (c : Compression) (g : SaltArray → OracleComp World α)
    (event : α → Prop) (p : Fin CounterSalt.groups → Block) : Strat Word1600 Bool :=
  (toStrat c (g (CounterSalt.nonceAt p))).bind (fun a => Strat.done (decide (event a)))

private theorem eager_event (π : Perm) (st : Strat Word1600 α) (event : α → Prop)
    [DecidablePred event] (s : PState Word1600) :
    (st.bind (fun a => .done (decide (event a)))).eager π s (fun b _ => accept b) =
      st.eager π s (fun a _ => ind (event a)) := by
  induction st generalizing s with
  | done a => by_cases h : event a <;> simp [Strat.bind,Strat.eager,accept,h,ind]
  | fwd x k ih => exact ih _ _
  | inv y k ih => exact ih _ _
  | rand m k ih => exact avg_congr (fun i _ => ih i _)

private theorem sample_event (c : Compression) (π : Perm) (g : SaltArray → OracleComp World α)
    (event : α → Prop) (p : Fin CounterSalt.groups → Block) :
    (prEvent (event <$> fixedOracleRun ⟨c,π⟩ (g (CounterSalt.nonceAt p)))).toReal =
      (eventStrategy c g event p).eager π PState.init (fun b _ => accept b) := by
  classical
  rw [fixed_run_prob c π _ event PState.init,
    ENNReal.toReal_ofReal (Strat.eager_nonneg _ (fun _ _ => ind_nonneg _) _ _)]
  exact (eager_event π (toStrat c (g (CounterSalt.nonceAt p))) event PState.init).symm

private theorem real_event (c : Compression) (g : SaltArray → OracleComp World α) (e : α → Prop) :
    (prEvent (e <$> counterNonceGame c g)).toReal =
      CounterSalt.realProb CounterSalt.splitReply CounterSalt.input (eventStrategy c g e) := by
  unfold counterNonceGame CounterSalt.realProb
  rw [uniform_mean]
  apply avg_congr
  intro π _
  rw [uniform_mean]
  apply avg_congr
  intro k _
  exact sample_event c π g e _

private theorem ideal_event (c : Compression) (g : SaltArray → OracleComp World α) (e : α → Prop) :
    (prEvent (e <$> iidNonceGame c g)).toReal = idealProb (eventStrategy c g e) := by
  unfold iidNonceGame idealProb
  rw [uniform_mean]
  let f := fun r : SaltArray =>
    (prEvent (e <$> (($ᵗ Perm) >>= fun π => fixedOracleRun ⟨c,π⟩ (g r)))).toReal
  rw [CounterSalt.iid_marginal f]
  apply avg_congr
  intro p _
  dsimp only [f]
  rw [uniform_mean,← Strat.avg_eager]
  apply avg_congr
  intro π _
  exact sample_event c π g e p

noncomputable def counterError (q : Nat) : ℝ := (CounterSalt.groups : ℝ) * ((2*q+CounterSalt.groups : ℝ)/2^192)

theorem counter_oracle_distance (c : Compression) (g : SaltArray → OracleComp World α) (q : Nat)
    (bound : ∀ r, PublicQueryBound (g r) q) :
    measureTVDist (counterNonceGame c g) (iidNonceGame c g) ≤ counterError q := by
  classical
  have event (e : α → Prop) :
      (prEvent (e <$> iidNonceGame c g)).toReal ≤
        (prEvent (e <$> counterNonceGame c g)).toReal + counterError q := by
    rw [real_event,ideal_event]
    have B (p : Fin CounterSalt.groups → Block) : (eventStrategy c g e p).QB q :=
      (to_strat_QB c (bound (CounterSalt.nonceAt p))).bind (fun a =>
        Strat.QB.done (decide (e a)) 0)
    have h := CounterSalt.ideal_le_counter CounterSalt.splitReply CounterSalt.input CounterSalt.key_injective CounterSalt.counter_distinct (eventStrategy c g e) q B
    have card : Fintype.card Key = 2^192 := by rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
    simpa only [counterError,card,Nat.cast_pow,Nat.cast_ofNat] using h
  apply tv_le_of_events _ _ _ (by unfold counterError; positivity)
  intro e
  have upper := event (fun a => ¬e a)
  rw [prEvent_not_eq_one_sub,prEvent_not_eq_one_sub,ENNReal.toReal_sub_of_le (prEvent_le_one _) ENNReal.one_ne_top,
    ENNReal.toReal_sub_of_le (prEvent_le_one _) ENNReal.one_ne_top,ENNReal.toReal_one] at upper
  have lower := event e
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end CommitGolfCandidate
