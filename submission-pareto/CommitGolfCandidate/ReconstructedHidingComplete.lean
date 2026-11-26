import CommitGolfCandidate.ReconstructedHidingChooser
import CommitGolfCandidate.ReconstructedHidingConclude

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingTraffic HidingReplay TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 2600000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false
attribute [local instance] keptKey keptReplies
attribute [local irreducible] markedBranch markedIndependent keyedGame chainPublicComp
local instance completeDiscrete {α : Type} : MeasurableSpace α := ⊤

theorem marked_deficit {S O : Type} {n q : Nat} (a : Hiding.HidingAdversary S O n) (bounded : Hiding.QueryBound a q)
    (build : TranscriptBuilder) (c : Compression) (range : q+1≤2^120) (ev : O → Prop) :
    deficit (markedPosterior a q build c false) (markedPosterior a q build c true) ev ≤ ((q:ℝ)+1)/2^120 := by
  let choose := lazyRun c a.choose (PermutationCache.empty Block)
  let next (w : Bool) (v : Hiding.HidingChallenge S n × Cache) :=
    ($ᵗ (Key × GenReplies)) >>= markedBranch a q build c w v.1 v.2
  refine deficit_bind_const choose (next false) (next true) ev _ ?_
  rintro ⟨ch,base⟩ reached
  obtain ⟨calls,used,cached,available⟩ := hiding_prefix_split a bounded c (ch,base) reached
  exact chooser_deficit a q build c ch base inferInstance calls cached used range available ev

theorem keyed_hiding {S O : Type} {n q : Nat} (a : Hiding.HidingAdversary S O n) (bounded : Hiding.QueryBound a q)
    (build : TranscriptBuilder) :
    measureTVDist (sampledKeyed a build false) (sampledKeyed a build true) ≤ min 1 (((q:ℝ)+1)/2^120) :=
  keyed_of_deficits a bounded build (fun c range ev => marked_deficit a bounded build c range ev)

theorem hiding_of_reconstructed_transcript (scheme : Scheme) (build : TranscriptBuilder)
    (refines : KeyedTranscriptRefines scheme build) : scheme.Hiding (fun _ q => min 1 (((q:ℝ)+1)/2^120)) :=
  scheme_hiding_of_keyed scheme build refines (fun a h => keyed_hiding a h build)

end CommitGolfCandidate.Reconstruction.HidingTape
