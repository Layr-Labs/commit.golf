import CommitGolfCandidate.ReconstructedHidingRestricted
import CommitGolfCandidate.SharedPinnedRestricted

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048
attribute [local irreducible] pinnedFirstAddresses pinnedCommonHigh

noncomputable def afterHiddenSampler {α : Type} (base : Cache) (positions : Positions)
    (sampler : ProbComp (UnopenedSalts positions)) (left right : Message) (opened : OpenedSalts positions) (which : Bool) (upper : Block → BitVec 1344)
    (observe : DigestTape → BiPermutation Block → ProbComp α) : ProbComp α := do
  let message := if which then right else left
  let salts ← sampler
  let final ← runPinnedFull base [] (pinnedConstantPlans (pinnedHiddenAddresses positions message upper salts))
  let p ← final.2.sample
  observe (fullDigestTape (pinnedOpenedDigestTape left upper opened p.val.forward)
    (pinnedHiddenDigestTape message upper salts p.val.forward)) p.val

noncomputable def restrictedHiddenSampler {α : Type} (base : Cache) (positions : Positions)
    (sampler : ProbComp (UnopenedSalts positions)) (left right : Message) (opened : OpenedSalts positions) (which : Bool)
    (observe : DigestTape → BiPermutation Block → ProbComp α) : ProbComp α :=
  pinnedCommonFull base positions left right opened (fun upper seeded =>
    afterHiddenSampler seeded positions sampler left right opened which upper observe)

theorem visible_hidden_sampler {α : Type} {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed] (positions : Positions)
    (sampler : ProbComp (UnopenedSalts positions)) (left right : Message) (opened : OpenedSalts positions) (which : Bool) (upper : Block → BitVec 1344)
    (visible : {i : Fin count // state.isRevealed i} → BitVec 256)
    (seen : ∀ i : {i : Index // i ∈ positions}, pinnedPublicAddress left upper i.val (opened i) ∈ state.opened)
    (observe : DigestTape → BiPermutation Block → ProbComp α) :
    (samplePinnedLowFn state.PrivateSlot >>= fun privateLow =>
      afterHiddenSampler (state.high.realize (pinnedFinLowTape (state.merge visible privateLow)))
        positions sampler left right opened which upper observe) =ᵈ
      (sampler >>= pinnedActualNonce state visible (Subtype.val : HiddenIndex positions → Index)
        (pinnedHiddenFirst positions (if which then right else left) upper)
        (fun i => messageWords (if which then right else left) i.val)
        (fun digest p => observe (fullDigestTape
          (pinnedOpenedDigestTape left upper opened (state.publicReply visible)) digest) p)) := by
  let message := if which then right else left
  let resume (privateLow : state.PrivateSlot → BitVec 256) (salt : UnopenedSalts positions) : ProbComp α := do
    let seed := state.high.realize (pinnedFinLowTape (state.merge visible privateLow))
    let final ← runPinnedFull seed [] (pinnedConstantPlans (pinnedHiddenAddresses positions message upper salt))
    let p ← final.2.sample
    observe (fullDigestTape (pinnedOpenedDigestTape left upper opened p.val.forward)
      (pinnedHiddenDigestTape message upper salt p.val.forward)) p.val
  apply (EvalDistEq.of_evalDist_eq (distribution_bind_comm (samplePinnedLowFn state.PrivateSlot)
    sampler resume)).trans
  apply EvalDistEq.bind_right
  intro salt
  apply EvalDistEq.bind_right
  intro privateLow
  let addr := pinnedHiddenAddresses positions message upper salt
  let seed := state.high.realize (pinnedFinLowTape (state.merge visible privateLow))
  apply EvalDistEq.bind_congr_of_support (runPinnedFull seed [] (pinnedConstantPlans addr))
  intro final reached
  apply EvalDistEq.bind_right
  intro p
  let restricted : Completion seed.entries :=
    ⟨p.val, fun row h => p.property row (pinned_full_preserves_rows seed [] (pinnedConstantPlans addr) final reached row h)⟩
  have openTape : pinnedOpenedDigestTape left upper opened p.val.forward =
      pinnedOpenedDigestTape left upper opened (state.publicReply visible) := by
    funext i
    exact congrArg pinnedOutputDigest
      (pinned_reference_public_reply state visible privateLow _ (seen i) restricted)
  let readAt := pinnedNonceOrder (Subtype.val : HiddenIndex positions → Index)
    (pinnedHiddenFirst positions message upper) (fun i => messageWords message i.val) salt
  have hiddenTape : pinnedHiddenDigestTape message upper salt p.val.forward =
      fun i => pinnedOutputDigest (p.val.forward addr[readAt.symm i]) := by
    funext i
    have atIndex := pinned_nonce_address_at (Subtype.val : HiddenIndex positions → Index)
      (pinnedHiddenFirst positions message upper) (fun j => messageWords message j.val) salt (readAt.symm i)
    change addr[readAt.symm i] =
      pinnedPublicAddress message upper (readAt (readAt.symm i)).val (salt (readAt (readAt.symm i))) at atIndex
    rw [readAt.apply_symm_apply] at atIndex
    exact congrArg (pinnedOutputDigest ∘ p.val.forward) atIndex.symm
  change observe (fullDigestTape (pinnedOpenedDigestTape left upper opened p.val.forward)
      (pinnedHiddenDigestTape message upper salt p.val.forward)) p.val =ᵈ
    observe (fullDigestTape (pinnedOpenedDigestTape left upper opened (state.publicReply visible))
      (fun i => pinnedOutputDigest (p.val.forward addr[readAt.symm i]))) p.val
  rw [openTape, hiddenTape]

theorem reorder_hidden_sampler {α : Type} (base : Cache) (positions : Positions)
    (sampler : ProbComp (UnopenedSalts positions)) (left right : Message) (opened : OpenedSalts positions) (which : Bool)
    (observe : DigestTape → BiPermutation Block → ProbComp α) :
    restrictedHiddenSampler base positions sampler left right opened which observe =ᵈ
      (sampler >>= fun closed =>
        pinnedClosedRestrictedWorld base positions left right opened closed which observe) := by
  let addresses := pinnedFirstAddresses left right
  let first := runPinnedFull base [] (pinnedConstantPlans addresses)
  let upper (cache : Cache) := pinnedBoundedHigh addresses cache
  let openedRun (cache : Cache) :=
    runPinnedFull cache [] (pinnedConstantPlans (pinnedOpenedAddresses positions left (upper cache) opened))
  let resume (cache : Cache) (closed : UnopenedSalts positions) (seed : Cache) := do
    let message := if which then right else left
    let final ← runPinnedFull seed [] (pinnedConstantPlans (pinnedHiddenAddresses positions message (upper cache) closed))
    let p ← final.2.sample
    observe (fullDigestTape (pinnedOpenedDigestTape left (upper cache) opened p.val.forward)
      (pinnedHiddenDigestTape message (upper cache) closed p.val.forward)) p.val
  let sample := sampler
  trans (do let a ← first
            let closed ← sample
            let b ← openedRun a.2
            resume a.2 closed b.2)
  · unfold restrictedHiddenSampler pinnedCommonFull
    apply EvalDistEq.bind_right first
    intro a
    exact (EvalDistEq.of_evalDist_eq (distribution_bind_comm sample (openedRun a.2)
      (fun closed b => resume a.2 closed b.2))).symm
  · exact (EvalDistEq.of_evalDist_eq (distribution_bind_comm sample first
      (fun closed a => openedRun a.2 >>= fun b => resume a.2 closed b.2))).symm

end CommitGolfCandidate.Reconstruction.HidingTape
