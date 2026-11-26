import CommitGolfCandidate.ReconstructedHidingCommon
import CommitGolfCandidate.ReconstructedHidingIntegrate
import CommitGolfCandidate.ReconstructedHidingPositiveGame

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingReplay HidingTraffic CommitGolfCandidate.Permutation
open CommitGolfCandidate.Permutation.NonceChain (mean accept Fresh)
set_option linter.unusedSectionVars false
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048
local instance retainedDiscrete {α : Type} : MeasurableSpace α := ⊤

abbrev GenReplies := Fin groupCount → Reply
abbrev GenTrace := PState Reply
noncomputable def tapeFromReplies (y : GenReplies) := selectedSalts (publicBlocks blockSplit y)

open Classical in
noncomputable def retainedEvent {A : Type} (c : Compression) (g : PrivateSalts → OracleComp World A)
    (ev : A → Prop) (keep : Key → GenReplies → GenTrace → Prop) : ℝ :=
  mean fun k => mean fun y => (toStrat c (g (tapeFromReplies y))).exp PState.init
    (fun a st => ind (ev a ∧ keep k y st))

attribute [local irreducible] Fresh packedAddress blockSplit selectedSalts toStrat fixedOracleRun

/-- Keeping only independent runs that leave the prescribed generator rows
fresh gives a subprobability of the actual shared-permutation game. The keep
predicate may also remove hidden-leaf hits. -/
theorem retained_event_le {A : Type} (c : Compression) (g : PrivateSalts → OracleComp World A)
    (ev : A → Prop) (keep : Key → GenReplies → GenTrace → Prop)
    (fresh : ∀ k y st, keep k y st → Fresh (scheduled (packedAddress k) y) st.trace) :
    retainedEvent c g ev keep ≤ (Pr{let a ← keyedGame c g}[ev a]).toReal := by
  classical
  let strategy (p : Parts) := (toStrat c (g (selectedSalts p))).bind (fun a => .done (decide (ev a)))
  have actual : realRun blockSplit packedAddress strategy = (Pr{let a ← keyedGame c g}[ev a]).toReal :=
    (keyed_event_exact c g ev).symm
  rw [←actual,←schedule_weight blockSplit packedAddress strategy]
  unfold retainedEvent
  rw [←avg_mul_left]
  apply avg_mono
  intro k _
  rw [←avg_mul_left]
  apply avg_mono
  intro y _
  have lower := common_row_lower (strategy (publicBlocks blockSplit y)) (scheduled (packedAddress k) y)
    (keep k y) (fresh k y)
  simp only [scheduled,List.length_ofFn] at lower ⊢
  refine le_trans ?_ lower
  dsimp only [strategy]
  rw [Strat.exp_bind]
  apply Strat.exp_mono
  intro a st
  by_cases value : ev a <;> simp [value,Strat.exp,ind]

end CommitGolfCandidate.Reconstruction.HidingTape
