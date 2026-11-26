import CommitGolfCandidate.ReconstructedHidingKeyed
import CommitGolfCandidate.NonceChainOracle

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp OracleSpec CommitGolfCandidate.Permutation
open CommitGolfCandidate.Permutation.NonceChain CommitGolfCandidate.Reconstruction.HidingReplay
set_option maxRecDepth 12000
set_option exponentiation.threshold 2048
local instance keyedDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

def blockNumber (p : Group) : Fin groupCount :=
  ⟨342*p.1.val+p.2.val,by have := p.1.isLt; have := p.2.isLt; unfold groupCount; omega⟩

theorem blockNumber_index (i : Fin groupCount) : blockNumber (groupIndex i) = i :=
  Fin.ext (by simp only [blockNumber,groupIndex]; omega)

theorem index_blockNumber (p : Group) : groupIndex (blockNumber p) = p := by
  obtain ⟨t,g⟩ := p
  have h := g.isLt
  apply Prod.ext <;> apply Fin.ext <;> simp only [groupIndex,blockNumber] <;> omega

abbrev PrivateSalts := Position → Salt
abbrev Parts := Fin groupCount → SaltBlock

def numberedBlocks (p : Parts) : Blocks := fun t g => p (blockNumber (t,g))
def selectedSalts (p : Parts) : PrivateSalts := select (numberedBlocks p)

def partsEquiv : Parts ≃ PrivateSalts × Slack where
  toFun p := (selectedSalts p, unused (numberedBlocks p))
  invFun pair i := assemble pair.1 pair.2 (groupIndex i).1 (groupIndex i).2
  left_inv p := by
    funext i
    dsimp only [selectedSalts]
    rw [assemble_select]
    simp only [numberedBlocks,Prod.mk.eta,blockNumber_index]
  right_inv pair := by
    have restore : numberedBlocks (fun i => assemble pair.1 pair.2 (groupIndex i).1 (groupIndex i).2) =
        assemble pair.1 pair.2 := by
      funext t g
      simp only [numberedBlocks,index_blockNumber]
    apply Prod.ext
    · exact (congrArg select restore).trans (select_assemble _ _)
    · exact (congrArg unused restore).trans (unused_assemble _ _)

theorem salts_marginal (f : PrivateSalts → ℝ) :
    mean f = mean (fun p : Parts => f (selectedSalts p)) := by
  have prod := mean_prod (fun r (_ : Slack) => f r)
  simp only [mean, avg_const Finset.univ_nonempty] at prod
  exact prod.symm.trans (mean_equiv partsEquiv (fun z => f z.1)).symm

noncomputable def generatedSalts (π : Perm) (k : Generator.Key) : PrivateSalts :=
  selectedSalts (publicBlocks blockSplit (fun i => π (packedAddress k i)))

variable {α : Type}
noncomputable local instance keySampler : SampleableType Generator.Key :=
  by classical exact SampleableType.ofFintype _
noncomputable local instance saltsSampler : SampleableType PrivateSalts :=
  by classical exact SampleableType.ofFintype _

noncomputable def keyedGame (c : Compression) (g : PrivateSalts → OracleComp World α) : ProbComp α := do
  let π ← $ᵗ Perm
  let k ← $ᵗ Generator.Key
  fixedOracleRun ⟨c,π⟩ (g (generatedSalts π k))

noncomputable def independentGame (c : Compression) (g : PrivateSalts → OracleComp World α) : ProbComp α := do
  let r ← $ᵗ PrivateSalts
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
private noncomputable def eventStrategy (c : Compression) (g : PrivateSalts → OracleComp World α)
    (event : α → Prop) (p : Parts) : Strat Word1600 Bool :=
  (toStrat c (g (selectedSalts p))).bind (fun a => Strat.done (decide (event a)))

private theorem eager_event (π : Perm) (st : Strat Word1600 α) (event : α → Prop)
    [DecidablePred event] (s : PState Word1600) :
    (st.bind (fun a => .done (decide (event a)))).eager π s (fun b _ => accept b) =
      st.eager π s (fun a _ => ind (event a)) := by
  induction st generalizing s with
  | done a => by_cases h : event a <;> simp [Strat.bind,Strat.eager,accept,h,ind]
  | fwd x k ih => exact ih _ _
  | inv y k ih => exact ih _ _
  | rand m k ih => exact avg_congr (fun i _ => ih i _)

private theorem sample_event (c : Compression) (π : Perm) (g : PrivateSalts → OracleComp World α)
    (event : α → Prop) (p : Parts) :
    (prEvent (event <$> fixedOracleRun ⟨c,π⟩ (g (selectedSalts p)))).toReal =
      (eventStrategy c g event p).eager π PState.init (fun b _ => accept b) := by
  classical
  rw [fixed_run_prob c π _ event PState.init,
    ENNReal.toReal_ofReal (Strat.eager_nonneg _ (fun _ _ => ind_nonneg _) _ _)]
  exact (eager_event π (toStrat c (g (selectedSalts p))) event PState.init).symm

private theorem real_event (c : Compression) (g : PrivateSalts → OracleComp World α) (e : α → Prop) :
    (prEvent (e <$> keyedGame c g)).toReal =
      realRun blockSplit packedAddress (eventStrategy c g e) := by
  unfold keyedGame realRun
  rw [uniform_mean]
  apply avg_congr
  intro π _
  rw [uniform_mean]
  apply avg_congr
  intro k _
  exact sample_event c π g e _

open Classical in
theorem keyed_event_exact (c : Compression) (g : PrivateSalts → OracleComp World α) (e : α → Prop) :
    (Pr{let a ← keyedGame c g}[e a]).toReal = realRun blockSplit packedAddress (fun p =>
      (toStrat c (g (selectedSalts p))).bind (fun a => .done (decide (e a)))) := real_event c g e

private theorem ideal_event (c : Compression) (g : PrivateSalts → OracleComp World α) (e : α → Prop) :
    (prEvent (e <$> independentGame c g)).toReal = idealRun (eventStrategy c g e) := by
  unfold independentGame idealRun
  rw [uniform_mean]
  let f := fun r : PrivateSalts =>
    (prEvent (e <$> (($ᵗ Perm) >>= fun π => fixedOracleRun ⟨c,π⟩ (g r)))).toReal
  rw [salts_marginal f]
  apply avg_congr
  intro p _
  dsimp only [f]
  rw [uniform_mean,← Strat.avg_eager]
  apply avg_congr
  intro π _
  exact sample_event c π g e p

noncomputable def generatorError (q : Nat) : ℝ :=
  (q:ℝ)/2^192 + q/2^160 + (groupCount:ℝ)*groupCount/2^1440

theorem generator_distance (c : Compression) (g : PrivateSalts → OracleComp World α) (q : Nat)
    (bound : ∀ r, PublicQueryBound (g r) q) :
    measureTVDist (keyedGame c g) (independentGame c g) ≤ generatorError q := by
  classical
  have event (e : α → Prop) :
      (prEvent (e <$> independentGame c g)).toReal ≤
        (prEvent (e <$> keyedGame c g)).toReal + generatorError q := by
    rw [real_event,ideal_event]
    have B (p : Parts) : (eventStrategy c g e p).QB q :=
      (to_strat_QB c (bound (selectedSalts p))).bind (fun a =>
        Strat.QB.done (decide (e a)) 0)
    exact generator_switch q _ B
  apply tv_le_of_events _ _ _ (by unfold generatorError; positivity)
  intro e
  have upper := event (fun a => ¬e a)
  rw [prEvent_not_eq_one_sub,prEvent_not_eq_one_sub,ENNReal.toReal_sub_of_le (prEvent_le_one _) ENNReal.one_ne_top,
    ENNReal.toReal_sub_of_le (prEvent_le_one _) ENNReal.one_ne_top,ENNReal.toReal_one] at upper
  have lower := event e
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end CommitGolfCandidate.Reconstruction.HidingTape
