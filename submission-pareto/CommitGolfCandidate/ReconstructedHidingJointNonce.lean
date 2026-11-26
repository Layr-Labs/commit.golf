import CommitGolfCandidate.ReconstructedHidingJointLoss
import CommitGolfCandidate.ReconstructedHidingDeficit
import CommitGolfCandidate.ReconstructedHidingNonceWorld

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingTraffic TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 2400000
set_option exponentiation.threshold 2048
attribute [local instance] jointFnSampler
attribute [local irreducible] pairedRows pinnedRowsNonce checkedQueries genRows
local instance jointNonceDiscrete {α : Type} : MeasurableSpace α := ⊤

section World
variable {I A : Type} [Fintype I] [DecidableEq I] {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed]
    (visible : {i : Fin count // state.isRevealed i} → BitVec 256)
    (pos : I → Position) (first : Bool → I → Reply) (msg : Bool → I → TwoPermutationPrototype.Words 32)
    (blocks : (I → Salt) → Group → SaltBlock) (flag : Secrets I → Bool)
    (c : Compression) (obs : (I → BitVec 256) → OracleComp World A)

noncomputable def nonceObserver (s : Secrets I) (dg : I → BitVec 256) :=
  checkedQueries (genPermit s.1.1 (proposedReplies blocks s)) (obs dg) (flag s)

noncomputable def realJointNonce (w : Bool) (s : Secrets I) :=
  pinnedActualNonce state visible pos (first w) (msg w)
    (fun dg p => fixedOracleRun (fixedOracle c p) (nonceObserver blocks flag obs s dg)) (fun i => (s.1.2 i).setWidth 128)

noncomputable def changedJointNonce (w : Bool) (s : Secrets I) : ProbComp (A × Bool) := do
  let dg ← samplePinnedLowFn I
  let priv ← samplePinnedLowFn state.PrivateSlot
  let table := state.high.realize (pinnedFinLowTape (state.merge visible priv))
  changedRun c table (pairedRows state pos first msg dg s.1.2) (nonceObserver blocks flag obs s dg) w

noncomputable def jointMarkedSide (w : Bool) (dg : I → BitVec 256) (priv : state.PrivateSlot → BitVec 256) :=
  markedCache c (state.high.realize (pinnedFinLowTape (state.merge visible priv)))
    (drawRowSeed state pos first msg dg) (applyLeafRows w)
    (fun s => genPermit s.1.1.1 (proposedReplies blocks s.1)) (fun s => flag s.1) (obs dg)

theorem nonce_score_lower (valid : state.high.Valid count) (unique : Function.Injective pos)
    (room : state.high.zero.entries.length+Fintype.card I≤2^121)
    (fresh : ∀ s, flag s=true → ¬prefixHit base pos s.1.2)
    (away : ∀ w nonce addr, addr∈pinnedNonceAddresses pos (first w) (msg w) nonce → addr∉state.opened)
    (w : Bool) (s : Secrets I) (ev : A → Prop) :
    mass (changedJointNonce state visible pos first msg blocks flag c obs w s) (retained ev) ≤
      mass (realJointNonce state visible pos first msg blocks flag c obs w s) (retained ev) := by
  classical
  cases accepted : flag s with
  | true =>
    have clean := fresh s accepted
    let observer := nonceObserver blocks flag obs s
    have law := guarded_clean state visible pos first msg c observer valid unique room w s.1.2 clean (away w _)
    unfold guardedNonce guardedRows at law
    simp only [ite_eq_right clean] at law
    exact (congrArg ENNReal.toReal (law.prEvent_eq (retained ev))).symm.le
  | false =>
    have lost : mass (changedJointNonce state visible pos first msg blocks flag c obs w s) (retained ev) = 0 := by
      unfold changedJointNonce
      apply mass_bind_zero
      intro dg
      apply mass_bind_zero
      intro priv
      unfold changedRun
      apply mass_bind_zero
      intro rows
      apply mass_bind_zero
      intro p
      unfold mass nonceObserver
      rw [accepted,checked_closed_zero,ENNReal.toReal_zero]
    rw [lost]
    exact ENNReal.toReal_nonneg

theorem changed_nonce_order (w : Bool) :
    (($ᵗ (Secrets I)) >>= changedJointNonce state visible pos first msg blocks flag c obs w) =ᵈ
      (do let dg ← samplePinnedLowFn I
          let priv ← samplePinnedLowFn state.PrivateSlot
          jointMarkedSide state visible pos first msg blocks flag c obs w dg priv) := by
  let seeds := ($ᵗ (Secrets I))
  let digs := samplePinnedLowFn I
  let privs := samplePinnedLowFn state.PrivateSlot
  let finish (s : Secrets I) (dg : I → BitVec 256) (priv : state.PrivateSlot → BitVec 256) :=
    changedRun c (state.high.realize (pinnedFinLowTape (state.merge visible priv)))
      (pairedRows state pos first msg dg s.1.2) (nonceObserver blocks flag obs s dg) w
  apply (EvalDistEq.of_evalDist_eq (distribution_bind_comm seeds digs (fun s dg => privs >>= finish s dg))).trans
  apply EvalDistEq.bind_right digs
  intro dg
  apply (EvalDistEq.of_evalDist_eq (distribution_bind_comm seeds privs (fun s priv => finish s dg priv))).trans
  apply EvalDistEq.bind_right privs
  intro priv
  unfold jointMarkedSide markedCache drawRowSeed
  simp only [bind_assoc,pure_bind,applyLeafRows,Equiv.apply_symm_apply]
  rfl

theorem joint_nonce_deficit (valid : state.high.Valid count) (unique : Function.Injective pos)
    (room : state.high.zero.entries.length+Fintype.card I≤2^121)
    (fresh : ∀ s, flag s=true → ¬prefixHit base pos s.1.2)
    (away : ∀ w nonce addr, addr∈pinnedNonceAddresses pos (first w) (msg w) nonce → addr∉state.opened)
    (gate : Secrets I → Prop) (initial : ∀ s, gate s → flag s=true)
    (gives : ∀ s, gate s → Function.Injective (blocks s.1.2) ∧
       ∀ g hi, (reverseUpper state.high hi).isSome → signature (blocks s.1.2 g) ≠ tailSignature hi)
    (excludes : ∀ low row, row∈(state.high.realize low).entries → ∀ s, gate s → ∀ g,
      blockSplit.symm (blocks s.1.2 g,s.2 g)≠row.2)
    (q : Nat) (limited : ∀ dg, QueryBounded (obs dg) q) (small : q≤2^120) (ev : A → Prop) :
    let world := fun w => ($ᵗ (Secrets I)) >>= realJointNonce state visible pos first msg blocks flag c obs w
    deficit (world false) (world true) ev ≤ mass ($ᵗ (Secrets I)) (fun s => ¬gate s)+combinedPostError (Fintype.card I) q := by
  classical
  let seeds := ($ᵗ (Secrets I))
  let side := jointMarkedSide state visible pos first msg blocks flag c obs
  let ordered (w : Bool) := do
    let dg ← samplePinnedLowFn I
    let priv ← samplePinnedLowFn state.PrivateSlot
    side w dg priv
  let real (w : Bool) := seeds >>= realJointNonce state visible pos first msg blocks flag c obs w
  have lower (w : Bool) (event : A → Prop) : mass (ordered w) (retained event) ≤ mass (real w) (retained event) := by
    have eq := (changed_nonce_order state visible pos first msg blocks flag c obs w).prEvent_eq (retained event)
    refine (congrArg ENNReal.toReal eq).symm.le.trans ?_
    exact mass_bind_mono seeds _ _ _ (fun s _ => nonce_score_lower state visible pos first msg blocks flag c obs valid unique room fresh away w s event)
  have pair (dg : I → BitVec 256) (priv : state.PrivateSlot → BitVec 256) :
      deficit (side false dg priv) (side true dg priv) ev ≤ mass seeds (fun s => ¬gate s)+combinedPostError (Fintype.card I) q := by
    let low := pinnedFinLowTape (state.merge visible priv)
    let rows := drawRowSeed state pos first msg dg
    let table := state.high.realize low
    let common := jointlyMarked c table rows (joinedRows blocks gate) (fun s => gate s.1) (obs dg)
    have transfer (w : Bool) (event : A → Prop) : mass common (retained event) ≤ mass (side w dg priv) (retained event) :=
      joint_observer_lower c table rows blocks gate (obs dg) event w (fun s => flag s.1) (fun s _ => initial s.1)
    exact (deficit_common common _ _ ev (transfer false ev) (transfer true _)).trans
      (joint_observer_loss state valid pos unique first msg dg room low blocks gate gives (excludes low) c (obs dg) q (limited dg) small)
  have orderedBound := deficit_bind_const (samplePinnedLowFn I) _ _ ev _ (fun dg _ =>
    deficit_bind_const (samplePinnedLowFn state.PrivateSlot) (side false dg) (side true dg) ev _ (fun priv _ => pair dg priv))
  change deficit (real false) (real true) ev ≤ _
  have left := lower false ev
  have right := lower true (fun x => ¬ev x)
  change deficit (ordered false) (ordered true) ev ≤ _ at orderedBound
  unfold deficit at orderedBound ⊢
  linarith only [left,right,orderedBound]

end World
end CommitGolfCandidate.Reconstruction.HidingTape
