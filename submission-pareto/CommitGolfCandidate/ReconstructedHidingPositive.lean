import CommitGolfCandidate.ReconstructedHidingNonceWorld

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp TwoPermutationPrototype.Sampling HidingTraffic
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false
local instance positiveDiscrete {α : Type} : MeasurableSpace α := ⊤
noncomputable local instance scanSalts {I : Type} [Fintype I] : SampleableType (I → Salt) :=
  by classical exact SampleableType.ofFintype _

noncomputable def wideSaltSample (I : Type) [Fintype I] : ProbComp (I → BitVec 128) :=
  (fun (s : I → Salt) i => (s i).setWidth 128) <$> ($ᵗ (I → Salt))

noncomputable def postError (n q : Nat) : ℝ :=
  (q:ℝ)*(rowRate n+(2*n:ℝ)/((2:ℝ)^1600-2^122))

theorem post_nonnegative (n q : Nat) : 0 ≤ postError n q := by
  unfold postError rowRate
  positivity

theorem conditional_positive {I A : Type} [Fintype I] [DecidableEq I] (base : Cache)
    (c : Compression) (q : Nat) (small : q ≤ 2^120) :
    ConditionalBound (A := A) base (wideSaltSample I) c q
      (postError (Fintype.card I) q + (base.entries.length:ℝ)/2^120) := by
  intro count state _ valid visible pos unique first msg room away obs limited
  let seed := ($ᵗ (I → Salt))
  let actual (w : Bool) (s : I → Salt) :=
    pinnedActualNonce state visible pos (first w) (msg w)
      (fun digest p => fixedOracleRun (fixedOracle c p) (obs digest)) (fun i => (s i).setWidth 128)
  let safe := guardedNonce state visible pos first msg c obs
  let prior := prefixHit base pos
  have cut := shared_exception seed prior actual safe
    (fun w s fresh => guarded_clean state visible pos first msg c obs valid unique room w s fresh (away w _))
    (fun s h => guarded_common state visible pos first msg c obs s h)
  have after : measureTVDist (seed >>= safe false) (seed >>= safe true) ≤ postError (Fintype.card I) q := by
    unfold measureTVDist
    rw [(guarded_reorder state visible pos first msg c obs false).evalDist_eq,
      (guarded_reorder state visible pos first msg c obs true).evalDist_eq]
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (post_nonnegative _ _)
    intro digest
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (post_nonnegative _ _)
    intro priv
    exact guarded_distance state valid pos unique first msg digest room (pinnedFinLowTape (state.merge visible priv))
      c (obs digest) q (limited digest) small
  have compare := cut.trans (add_le_add after (prefix_probability base pos unique))
  simpa only [wideSaltSample,bind_map_left,seed,actual,Function.comp_def] using compare

end CommitGolfCandidate.Reconstruction.HidingTape
