import CommitGolfCandidate.ReconstructedHidingFrameRestricted

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingTraffic HidingReplay TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 2600000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false
attribute [local instance] keptKey keptReplies
attribute [local irreducible] markedBranch markedIndependent keyedGame chainPublicComp
local instance finalDiscrete {α : Type} : MeasurableSpace α := ⊤

theorem mass_complement {A : Type} (d : ProbComp A) (ev : A → Prop) :
    mass d (fun x => ¬ev x)=1-mass d ev := by
  unfold mass
  rw [prEvent_not_eq_one_sub,ENNReal.toReal_sub_of_le (prEvent_le_one _) ENNReal.one_ne_top,ENNReal.toReal_one]

theorem compression_of_deficit {S O : Type} {n q : Nat} (a : Hiding.HidingAdversary S O n)
    (bounded : Hiding.QueryBound a q) (build : TranscriptBuilder) (c : Compression)
    (estimate : ∀ ev : O → Prop, deficit (markedPosterior a q build c false) (markedPosterior a q build c true) ev ≤ ((q:ℝ)+1)/2^120) :
    let game := fun w => keyedGame c (fun r => chainPublicComp a q build c w (widenTape r))
    measureTVDist (game false) (game true) ≤ ((q:ℝ)+1)/2^120 := by
  let g (w : Bool) := fun r => chainPublicComp a q build c w (widenTape r)
  let game (w : Bool) := keyedGame c (g w)
  let marked (w : Bool) := markedPosterior a q build c w
  have kept (w : Bool) (ev : O → Prop) : mass (marked w) (retained ev) ≤ mass (game w) ev := by
    have same := (marked_posterior_eq a q build c w).prEvent_eq (retained ev)
    exact (congrArg ENNReal.toReal same).symm.le.trans (marked_event_le c (g w) ev)
  have side (ev : O → Prop) : mass (game true) ev - mass (game false) ev ≤ ((q:ℝ)+1)/2^120 := by
    have bound := estimate ev
    change 1-mass (marked false) (retained ev)-mass (marked true) (retained (fun x => ¬ev x)) ≤ _ at bound
    have l := kept false ev
    have r := kept true (fun x => ¬ev x)
    rw [mass_complement] at r
    linarith only [l,r,bound]
  apply tv_le_of_events (game false) (game true) _ (by positivity)
  intro ev
  have other := side (fun a => ¬ev a)
  rw [mass_complement,mass_complement] at other
  change |mass (game false) ev-mass (game true) ev|≤_
  exact abs_sub_le_iff.mpr ⟨by linarith only [other],by linarith only [side ev]⟩

/-- The shared keyed 120-bit leaf tape satisfies the contest hiding bound for
every query budget and every opening cardinality. -/
theorem keyed_of_deficits {S O : Type} {n q : Nat} (a : Hiding.HidingAdversary S O n) (bounded : Hiding.QueryBound a q)
    (build : TranscriptBuilder)
    (estimate : ∀ c : Compression, q+1≤2^120 → ∀ ev : O → Prop,
      deficit (markedPosterior a q build c false) (markedPosterior a q build c true) ev ≤ ((q:ℝ)+1)/2^120) :
    measureTVDist (sampledKeyed a build false) (sampledKeyed a build true) ≤ min 1 (((q:ℝ)+1)/2^120) := by
  refine le_min (measureTVDist_le_one _ _) ?_
  by_cases range : q+1≤2^120
  · have law := measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression)
      (fun c => keyedGame c (fun r => chainPublicComp a q build c false (widenTape r)))
      (fun c => keyedGame c (fun r => chainPublicComp a q build c true (widenTape r)))
      (by positivity : (0:ℝ)≤((q:ℝ)+1)/2^120) (fun c => compression_of_deficit a bounded build c (estimate c range))
    simpa only [measureTVDist,keyed_grouped a bounded build false,keyed_grouped a bounded build true] using law
  · apply (measureTVDist_le_one _ _).trans
    have large : 2^120 ≤ q+1 := by omega
    have cast : (2:ℝ)^120 ≤ (q:ℝ)+1 := by exact_mod_cast large
    exact (le_div_iff₀ (by positivity : 0<(2:ℝ)^120)).mpr (by simpa using cast)

end CommitGolfCandidate.Reconstruction.HidingTape
