import CommitGolfCandidate.NoncePairLayout
import CommitGolfCandidate.NonceChainOracle

/-! Replace paired-generator salts by independent salts in an arbitrary bounded
public continuation. The oracle is shared with every forward/inverse query in
that continuation; only the generator's private key is independently sampled. -/
namespace CommitGolfCandidate.Permutation.NoncePair
open CommitGolf OracleComp OracleSpec
open NonceChain (mean)
local instance pairDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
set_option linter.unusedSectionVars false
set_option maxRecDepth 12000

variable {α : Type}
abbrev SaltArray := Index → BitVec 128

noncomputable def chainNonceGame (c : Compression) (g : SaltArray → OracleComp World α) : ProbComp α := do
  let π ← $ᵗ Perm
  let k ← $ᵗ Key
  fixedOracleRun ⟨c,π⟩ (g (actualNonces π k))

def iidNonceGame (c : Compression) (g : SaltArray → OracleComp World α) : ProbComp α := do
  let r ← $ᵗ SaltArray
  let π ← $ᵗ Perm
  fixedOracleRun ⟨c,π⟩ (g r)

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
    (event : α → Prop) (p : Fin blocks → Block) : Strat Word1600 Bool :=
  (toStrat c (g (nonceAt p))).bind (fun a => Strat.done (decide (event a)))

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
    (event : α → Prop) (p : Fin blocks → Block) :
    (prEvent (event <$> fixedOracleRun ⟨c,π⟩ (g (nonceAt p)))).toReal =
      (eventStrategy c g event p).eager π PState.init (fun b _ => accept b) := by
  classical
  rw [fixed_run_prob c π _ event PState.init,
    ENNReal.toReal_ofReal (Strat.eager_nonneg _ (fun _ _ => ind_nonneg _) _ _)]
  exact (eager_event π (toStrat c (g (nonceAt p))) event PState.init).symm

attribute [local irreducible] orbit pairedInput pairedReply

private theorem real_event (c : Compression) (g : SaltArray → OracleComp World α) (e : α → Prop) :
    (prEvent (e <$> chainNonceGame c g)).toReal =
      realProb blockEquiv seedState inputTransform (eventStrategy c g e) := by
  unfold chainNonceGame realProb
  rw [uniform_mean]
  apply avg_congr
  intro π _
  rw [uniform_mean]
  apply avg_congr
  intro k _
  let p : Fin blocks → Block := fun i =>
    (blockEquiv (orbit π inputTransform (seedState k) (i.val+1))).1
  have salts : actualNonces π k = nonceAt p := by
    unfold actualNonces
    apply congrArg nonceAt
    funext i
    exact congrArg (fun y => (blockEquiv y).1) (pairedReply_eq_orbit π k i.val)
  rw [salts]
  exact sample_event c π g e p

private theorem ideal_event (c : Compression) (g : SaltArray → OracleComp World α) (e : α → Prop) :
    (prEvent (e <$> iidNonceGame c g)).toReal = idealProb (eventStrategy c g e) := by
  unfold iidNonceGame idealProb
  rw [uniform_mean]
  let f := fun r : SaltArray =>
    (prEvent (e <$> (($ᵗ Perm) >>= fun π => fixedOracleRun ⟨c,π⟩ (g r)))).toReal
  rw [CommitGolfCandidate.iid_nonce_marginal f]
  apply avg_congr
  intro p _
  dsimp only [f]
  rw [uniform_mean,← Strat.avg_eager]
  apply avg_congr
  intro π _
  exact sample_event c π g e p

/-- The paired tape is statistically close to iid salts even when the public
continuation receives every salt and adaptively queries both oracle directions. -/
theorem nonce_chain_oracle_distance (c : Compression) (g : SaltArray → OracleComp World α) (q : Nat)
    (bound : ∀ r, PublicQueryBound (g r) q) :
    measureTVDist (chainNonceGame c g) (iidNonceGame c g) ≤ chainError q := by
  classical
  have event (e : α → Prop) :
      (prEvent (e <$> iidNonceGame c g)).toReal ≤
        (prEvent (e <$> chainNonceGame c g)).toReal + chainError q := by
    rw [real_event,ideal_event]
    have B (p : Fin blocks → Block) : (eventStrategy c g e p).QB q :=
      (to_strat_QB c (bound (nonceAt p))).bind (fun a =>
        Strat.QB.done (decide (e a)) 0)
    have h := ideal_le_real blockEquiv seedState inputTransform seed_injective
      input_encoder_injective (eventStrategy c g e) q B
    have card : Fintype.card Key = 2^192 := by rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
    simpa only [chainError,card,Nat.cast_pow,Nat.cast_ofNat] using h
  apply CommitGolfCandidate.tv_le_of_events _ _ _ (by unfold chainError; positivity)
  intro e
  have upper := event (fun a => ¬e a)
  rw [prEvent_not_eq_one_sub,prEvent_not_eq_one_sub,ENNReal.toReal_sub_of_le (prEvent_le_one _) ENNReal.one_ne_top,
    ENNReal.toReal_sub_of_le (prEvent_le_one _) ENNReal.one_ne_top,ENNReal.toReal_one] at upper
  have lower := event e
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end CommitGolfCandidate.Permutation.NoncePair
