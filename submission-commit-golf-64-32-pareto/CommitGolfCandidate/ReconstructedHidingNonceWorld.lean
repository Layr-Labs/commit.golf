import CommitGolfCandidate.ReconstructedHidingProtected
import CommitGolfCandidate.ReconstructedHidingGuard
import CommitGolfCandidate.ReconstructedHidingConditionalLift

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp TwoPermutationPrototype.Sampling HidingTraffic
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false
local instance nonceWorldDiscrete {α : Type} : MeasurableSpace α := ⊤
noncomputable local instance worldSalt {I : Type} [Fintype I] : SampleableType (I → Salt) :=
  by classical exact SampleableType.ofFintype _

section World
variable {I A : Type} [Fintype I] {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    [DecidablePred state.isRevealed] (visible : {i : Fin count // state.isRevealed i} → BitVec 256)
    (pos : I → Position) (first : Bool → I → Reply) (msg : Bool → I → TwoPermutationPrototype.Words 32)
    (c : Compression) (obs : (I → BitVec 256) → OracleComp World A)

attribute [local irreducible] pinnedRowsNonce runPinnedHigh

omit [DecidablePred state.isRevealed] in
theorem paired_project (s : I → Salt) (digest : I → BitVec 256) (w : Bool) :
    (sideRows w <$> pairedRows state pos first msg digest s) =ᵈ
      pinnedRowsNonce state pos (first w) (msg w) digest (fun i => (s i).setWidth 128) := by
  let draw (w : Bool) := pinnedRowsNonce state pos (first w) (msg w) digest (fun i => (s i).setWidth 128)
  cases w with
  | false =>
    change (sideRows false <$> (draw false >>= fun l => draw true >>= fun r => pure (l,r))) =ᵈ draw false
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,sideRows]
    trans (draw false >>= pure)
    · apply EvalDistEq.bind_right
      intro l
      exact EvalDistEq.of_evalDist_eq (evalDist_bind_const (draw true) (pure l))
    · rw [bind_pure]
  | true =>
    change (sideRows true <$> (draw false >>= fun l => draw true >>= fun r => pure (l,r))) =ᵈ draw true
    simp only [map_eq_bind_pure_comp,bind_assoc,pure_bind,Function.comp_def,sideRows,ite_true,bind_pure]
    exact EvalDistEq.of_evalDist_eq (evalDist_bind_const (draw false) (draw true))

noncomputable def guardedNonce (w : Bool) (s : I → Salt) : ProbComp A := do
  let digest ← samplePinnedLowFn I
  let priv ← samplePinnedLowFn state.PrivateSlot
  let table := state.high.realize (pinnedFinLowTape (state.merge visible priv))
  changedRun c table (guardedRows state pos first msg digest s) (obs digest) w

theorem guarded_clean (valid : state.high.Valid count) (unique : Function.Injective pos)
    (room : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (w : Bool) (s : I → Salt) (clear : ¬prefixHit base pos s)
    (away : ∀ a ∈ pinnedNonceAddresses pos (first w) (msg w) (fun i => (s i).setWidth 128), a ∉ state.opened) :
    pinnedActualNonce state visible pos (first w) (msg w)
      (fun digest p => fixedOracleRun (fixedOracle c p) (obs digest)) (fun i => (s i).setWidth 128) =ᵈ
        guardedNonce state visible pos first msg c obs w s := by
  apply (pinned_actual_nonce_programmed state visible pos (first w) (msg w) _ valid unique _ room away
    (prefix_fresh base pos (first w) (msg w) s clear)).trans
  unfold guardedNonce pinnedProgrammedNonce
  apply EvalDistEq.bind_right (samplePinnedLowFn I)
  intro digest
  unfold samplePinnedBasePermutation
  simp only [bind_assoc,pure_bind]
  apply EvalDistEq.bind_right (samplePinnedLowFn state.PrivateSlot)
  intro priv
  let table := state.high.realize (pinnedFinLowTape (state.merge visible priv))
  let draw := pairedRows state pos first msg digest s
  let finish (p : Completion table.entries) (r : Paired) :=
    fixedOracleRun (fixedOracle c (p.val.programRows (sideRows w r))) (obs digest)
  unfold changedRun guardedRows
  rw [ite_eq_right clear]
  trans (table.sample >>= fun p => draw >>= fun r => finish p r)
  · apply EvalDistEq.bind_right table.sample
    intro p
    let next (rows : List Row) := fixedOracleRun (fixedOracle c (p.val.programRows rows)) (obs digest)
    have law := ((paired_project state pos first msg s digest w).symm.bind_left next)
    rw [bind_map_left] at law
    exact law
  · exact EvalDistEq.of_evalDist_eq (distribution_bind_comm table.sample draw finish)

theorem guarded_common (s : I → Salt) (hit : prefixHit base pos s) :
    guardedNonce state visible pos first msg c obs false s =ᵈ guardedNonce state visible pos first msg c obs true s := by
  classical
  unfold guardedNonce
  apply EvalDistEq.bind_right
  intro digest
  apply EvalDistEq.bind_right
  intro priv
  unfold changedRun guardedRows
  rw [ite_eq_left hit]
  simp only [pure_bind,sideRows,ite_self]
  exact EvalDistEq.refl _

theorem guarded_reorder (w : Bool) :
    (($ᵗ (I → Salt)) >>= guardedNonce state visible pos first msg c obs w) =ᵈ
      (do let digest ← samplePinnedLowFn I
          let priv ← samplePinnedLowFn state.PrivateSlot
          let table := state.high.realize (pinnedFinLowTape (state.merge visible priv))
          changedRun c table (guardedSample state pos first msg digest) (obs digest) w) := by
  let seed := ($ᵗ (I → Salt))
  let draws := samplePinnedLowFn I
  let lows := samplePinnedLowFn state.PrivateSlot
  let finish (s : I → Salt) (digest : I → BitVec 256) (priv : state.PrivateSlot → BitVec 256) :=
    changedRun c (state.high.realize (pinnedFinLowTape (state.merge visible priv)))
      (guardedRows state pos first msg digest s) (obs digest) w
  apply (EvalDistEq.of_evalDist_eq (distribution_bind_comm seed draws (fun s d => lows >>= finish s d))).trans
  apply EvalDistEq.bind_right draws
  intro digest
  apply (EvalDistEq.of_evalDist_eq (distribution_bind_comm seed lows (fun s p => finish s digest p))).trans
  apply EvalDistEq.bind_right lows
  intro priv
  simp only [finish,changedRun,guardedSample,bind_assoc,seed]
  rfl

end World

end CommitGolfCandidate.Reconstruction.HidingTape
