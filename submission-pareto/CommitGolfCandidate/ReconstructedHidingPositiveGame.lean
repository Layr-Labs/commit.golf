import CommitGolfCandidate.ReconstructedHidingPositive

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 2200000
set_option exponentiation.threshold 2048
local instance gameDiscrete {α : Type} : MeasurableSpace α := ⊤
noncomputable local instance gameClosed (p : Positions) : SampleableType (ClosedIx p → Salt) :=
  by classical exact SampleableType.ofFintype _

private theorem after_budget (n q t seen : Nat) (size : n ≤ LENGTH) (used : t ≤ q) (cache : seen ≤ t) :
    postError n (q-t) + (seen:ℝ)/2^120 ≤ postError LENGTH q := by
  let extra (n : Nat) : ℝ := 2*(n:ℝ)/2^1343 + 2*(n:ℝ)/((2:ℝ)^1600-2^122)
  have z (n : Nat) : 0 ≤ extra n := by unfold extra; positivity
  have cost (n t : Nat) : postError n t = (t:ℝ)*(1/2^120+extra n) := by
    unfold postError rowRate extra
    ring
  have hlen : (n:ℝ) ≤ LENGTH := by exact_mod_cast size
  have mul : extra n ≤ extra LENGTH := by
    unfold extra
    gcongr
  have total : ((q-t:Nat):ℝ)+(t:ℝ)=q := by exact_mod_cast Nat.sub_add_cancel used
  have hit : (seen:ℝ) ≤ t := by exact_mod_cast cache
  have subtotal := mul_le_mul_of_nonneg_left mul (Nat.cast_nonneg (q-t) : (0:ℝ)≤((q-t:Nat):ℝ))
  have prev := mul_nonneg (Nat.cast_nonneg t : (0:ℝ)≤t) (z LENGTH)
  rw [cost,cost]
  rw [←total]
  nlinarith

attribute [local irreducible] ConditionalBound restrictedHiddenSampler pinnedClosedRestrictedWorld

theorem restricted_positive {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : TranscriptBuilder) (c : Compression) (q : Nat) (bounded : Hiding.QueryBound a q) (range : q+1 ≤ 2^120) :
    measureTVDist (restrictedPosterior a build c false) (restrictedPosterior a build c true) ≤ postError LENGTH q := by
  unfold restrictedPosterior
  apply pinned_restricted_bind_support_le (lazyRun c a.choose (PermutationCache.empty Block)) _ _ _ (post_nonnegative _ _)
  rintro ⟨ch,base⟩ reached
  obtain ⟨calls,total,cache,observerBound⟩ := hiding_prefix_split a bounded c (ch,base) reached
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (post_nonnegative _ _)
  intro op
  let p := ch.positions
  let sampler := wideSaltSample (HiddenIndex ch.positions)
  let opened := wideOpen op
  let observer (tape : DigestTape) :=
    let view := build c ch.positions opened tape
    a.observe ch.aux view.1 view.2
  let execute := fun tape perm => fixedOracleRun (fixedOracle c perm) (observer tape)
  let small (which : Bool) :=
    restrictedHiddenSampler base ch.positions sampler ch.message₀ ch.message₁ opened which execute
  have each (w : Bool) : small w =ᵈ
      (($ᵗ (ClosedIx ch.positions → Salt)) >>= fun cl =>
        pinnedClosedRestrictedWorld base ch.positions ch.message₀ ch.message₁ opened (wideClosed cl) w execute) := by
    apply (reorder_hidden_sampler base ch.positions sampler ch.message₀ ch.message₁ opened w execute).trans
    dsimp only [sampler,wideSaltSample]
    rw [bind_map_left]
    exact @uniform_transport_bind (HiddenIndex ch.positions → Salt) (ClosedIx ch.positions → Salt) O
      (scanSalts (I := HiddenIndex ch.positions)) (gameClosed ch.positions) (transportOfEquiv (Equiv.refl _))
      (fun cl => pinnedClosedRestrictedWorld base ch.positions ch.message₀ ch.message₁ opened (wideClosed cl) w execute)
  have bound : ∀ digest, QueryBounded (observer digest) (q-calls) := by
    intro digest
    simpa only [observer] using observerBound (build c ch.positions opened digest).1
      (build c ch.positions opened digest).2
  have room : base.entries.length + 3*LENGTH ≤ 2^121 := by
    have len : LENGTH = 2^24 := rfl
    change base.entries.length ≤ calls at cache
    omega
  let n := Fintype.card (HiddenIndex ch.positions)
  let eps := postError n (q-calls) + (base.entries.length:ℝ)/2^120
  have positive : 0 ≤ eps := add_nonneg (post_nonnegative _ _) (by positivity)
  have rest : q-calls ≤ 2^120 := by omega
  have cond := conditional_positive (I := HiddenIndex ch.positions) (A := O) base c (q-calls) rest
  have compared : measureTVDist (small false) (small true) ≤ eps :=
    restricted_from_conditional base ch.positions ch.message₀ ch.message₁ opened c observer sampler (q-calls) bound
      eps positive cond room
  have len : n ≤ LENGTH := by
    have hc := hidden_index_count ch.positions
    rw [hiddenIndices,Finset.length_toList,Finset.card_univ] at hc
    change Fintype.card (HiddenIndex ch.positions) ≤ 2^24
    omega
  have all := compared.trans (after_budget n q calls base.entries.length len total cache)
  unfold measureTVDist at all ⊢
  rw [(each false).evalDist_eq,(each true).evalDist_eq] at all
  exact all

theorem independent_positive {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : TranscriptBuilder) (q : Nat) (bounded : Hiding.QueryBound a q) (small : q+1 ≤ 2^120) :
    measureTVDist (sampledIndependent a build false) (sampledIndependent a build true)
      ≤ 2*restrictedError q + postError LENGTH q := by
  have per (c : Compression) : measureTVDist (independentReference a build c false)
      (independentReference a build c true) ≤ 2*restrictedError q + postError LENGTH q := by
    let actual := independentPosterior a build c
    let restricted := restrictedPosterior a build c
    have left : measureTVDist (actual false) (restricted false) ≤ restrictedError q := by
      rw [measureTVDist_comm]
      exact restricted_distance a build c false q bounded small
    have right := restricted_distance a build c true q bounded small
    have both := restricted_positive a build c q bounded small
    have total := (measureTVDist_triangle (actual false) (restricted false) (actual true)).trans
      (add_le_add left ((measureTVDist_triangle (restricted false) (restricted true) (actual true)).trans
        (add_le_add both right)))
    unfold measureTVDist
    rw [(independent_eager_posterior a build c false).evalDist_eq,(independent_eager_posterior a build c true).evalDist_eq]
    change measureTVDist (actual false) (actual true) ≤ _
    linarith
  unfold measureTVDist
  rw [(sampled_independent_reference a build false).evalDist_eq,(sampled_independent_reference a build true).evalDist_eq]
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (add_nonneg (by unfold restrictedError; positivity) (post_nonnegative _ _))
  exact per

theorem keyed_upto {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : TranscriptBuilder) (q : Nat) (bounded : Hiding.QueryBound a q) (small : q ≤ 2^38-2^25) :
    measureTVDist (sampledKeyed a build false) (sampledKeyed a build true) ≤ ((q:ℝ)+1)/(2:ℝ)^120 := by
  have left := keyed_reference_distance a bounded build false
  have right := keyed_reference_distance a bounded build true
  rw [measureTVDist_comm] at right
  have middle := independent_positive a build q bounded (by omega)
  have combined := (measureTVDist_triangle (sampledKeyed a build false) (sampledIndependent a build false) _).trans
    (add_le_add left ((measureTVDist_triangle _ (sampledIndependent a build true) (sampledKeyed a build true)).trans
      (add_le_add middle right)))
  refine combined.trans ?_
  norm_num [generatorError,restrictedError,postError,rowRate,groupCount,LENGTH,LOG_LENGTH,Nat.cast_mul,Nat.cast_add]
  have limit : (q:ℝ) ≤ 274844352512 := by exact_mod_cast small
  linarith only [limit]

end CommitGolfCandidate.Reconstruction.HidingTape
