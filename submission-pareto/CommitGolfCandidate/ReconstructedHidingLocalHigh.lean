import CommitGolfCandidate.ReconstructedHidingFrameRestricted

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingTraffic TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 2400000
set_option exponentiation.threshold 2048
attribute [local instance] jointFnSampler posteriorClosed
attribute [local irreducible] pinnedFirstAddresses pinnedCommonHigh guardedView
local instance highDiscrete {α : Type} : MeasurableSpace α := ⊤

private theorem transfer_seed {X A : Type} {sa sb : SampleableType X} {f g : X → ProbComp (A × Bool)}
    {ev : A → Prop} {bad : X → Prop} {cost : ℝ}
    (bound : deficit ((@uniformSample X sa) >>= f) ((@uniformSample X sa) >>= g) ev ≤ mass (@uniformSample X sa) bad + cost) :
    deficit ((@uniformSample X sb) >>= f) ((@uniformSample X sb) >>= g) ev ≤ mass (@uniformSample X sb) bad + cost := by
  have l := @uniform_transport_bind X X (A × Bool) sb sa (transportOfEquiv (Equiv.refl X)) f
  have r := @uniform_transport_bind X X (A × Bool) sb sa (transportOfEquiv (Equiv.refl X)) g
  unfold deficit mass at bound ⊢
  rw [l.prEvent_eq (retained ev),r.prEvent_eq (retained (fun x => ¬ev x)),@uniform_versions X sb sa bad]
  exact bound

theorem frame_high_deficit {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n) (q : Nat) (build : TranscriptBuilder)
    (c : Compression) (ch : Hiding.HidingChallenge S n) (base : Cache) (v : VisibleGenerator ch.positions)
    (cap : base.entries.length+3*LENGTH ≤ 2^121) (st : PinnedCommonHigh base)
    (reached : st∈support (pinnedCommonHigh base ch.positions ch.message₀ ch.message₁ (wideOpen v.1)))
    (after : Nat) (small : after≤2^120) (budget : ∀ ds, QueryBounded (guardedObserver a q build c ch (wideOpen v.1) ds) after)
    (ev : O → Prop) :
    let seeds := ($ᵗ (Secrets (ClosedIx ch.positions)))
    let world := fun w => seeds >>= fun s => frameHigh a q build c ch base v s w st
    let gate := jointGate (pinnedFirstAddresses ch.message₀ ch.message₁) ch.positions v st.final
    deficit (world false) (world true) ev ≤ mass seeds (fun s => ¬gate s) +
      combinedPostError (Fintype.card (HiddenIndex ch.positions)) after := by
  classical
  let p := ch.positions
  let left := ch.message₀
  let right := ch.message₁
  let op := wideOpen v.1
  let xs := pinnedFirstAddresses left right
  have card : Fintype.card (HiddenIndex p)+p.card=LENGTH := by
    have h := hidden_index_count p
    rwa [hiddenIndices,Finset.length_toList,Finset.card_univ] at h
  have room : base.entries.length+2*LENGTH+p.card≤2^121 := by omega
  have facts := pinned_common_high_facts base p left right op room st reached
  let state := PinnedCommonHigh.openedState facts
  let upper := pinnedBoundedHigh xs st.first.zero
  have enough : state.high.zero.entries.length+Fintype.card (HiddenIndex p)≤2^121 := by
    have size := facts.tableBound
    change state.high.zero.entries.length≤base.entries.length+2*LENGTH+p.card at size
    omega
  have matchOpen : pinnedOpenedAddresses p left upper op=state.opened := by
    rw [show state.opened=st.opened from rfl,facts.openedShape]
    apply pinned_bound_high_opened
    exact fun i _ => pinned_first_address_mem left right false i
  have seen (i : {i : Index // i∈p}) : pinnedPublicAddress left upper i.val (op i)∈state.opened := by
    rw [←matchOpen]
    refine List.mem_map.mpr ⟨i.val,Finset.mem_toList.mpr i.property,?_⟩
    simp only [publicOpenedSalts,dite_eq_left i.property]
  let first := fun w : Bool => pinnedHiddenFirst p (if w then right else left) upper
  let msg := fun (w : Bool) (i : HiddenIndex p) => messageWords (if w then right else left) i.val
  let pos := (Subtype.val : HiddenIndex p → Index)
  have away (w : Bool) (nonce : UnopenedSalts p) (addr : Block)
      (found : addr∈pinnedNonceAddresses pos (first w) (msg w) nonce) : addr∉state.opened := by
    rw [←matchOpen]
    exact pinned_hidden_addresses_away left (if w then right else left) upper upper op nonce addr found
  let seed := ($ᵗ (Secrets (ClosedIx ch.positions)))
  let vis := samplePinnedLowFn {i : Fin (2*LENGTH+p.card) // state.isRevealed i}
  let blocks := knownBlocks p v.1 v.2
  let flag := frameFlag base xs p v
  let gate := jointGate xs p v st.final
  let observe := guardedObserver a q build c ch op
  let publicRun (visible : {i : Fin (2*LENGTH+p.card) // state.isRevealed i} → BitVec 256)
      (dg : HiddenIndex p → BitVec 256) :=
    observe (fullDigestTape (pinnedOpenedDigestTape left upper op (state.publicReply visible)) dg)
  let actual w visible := realJointNonce state visible pos first msg blocks flag c (publicRun visible) w
  have fixed (w : Bool) (s : Secrets (ClosedIx p)) :
      frameHigh a q build c ch base v s w st =ᵈ (vis >>= fun visible => actual w visible s) := by
    let next := frameAfter a q build c ch base v s w upper
    apply (pinned_opened_lows_equivalence state next).trans
    apply EvalDistEq.bind_right vis
    intro visible
    have h := visible_hidden_sampler state p (pure (wideClosed s.1.2)) left right op w upper visible seen
      (frameObserve a q build c ch base v s)
    rw [pure_bind] at h
    exact h
  have order (w : Bool) : (seed >>= fun s => frameHigh a q build c ch base v s w st) =ᵈ
      (vis >>= fun visible => seed >>= actual w visible) := by
    apply (EvalDistEq.bind_right seed (fixed w)).trans
    exact EvalDistEq.of_evalDist_eq (distribution_bind_comm seed vis (fun s visible => actual w visible s))
  have paid (visible : {i : Fin (2*LENGTH+p.card) // state.isRevealed i} → BitVec 256) :
      deficit (seed >>= actual false visible) (seed >>= actual true visible) ev ≤
        mass seed (fun s => ¬gate s) + combinedPostError (Fintype.card (HiddenIndex p)) after := by
    have gate_to_base (s : Secrets (ClosedIx p)) (pass : gate s) : flag s=true :=
      @decide_eq_true (baseGood base xs ((openingGenerators p).symm (v,s))) (Classical.propDecidable _) pass.1
    have noOld (s : Secrets (ClosedIx p)) (pass : flag s=true) : ¬prefixHit base pos s.1.2 :=
      base_closed_safe base xs p v s (@of_decide_eq_true (baseGood base xs ((openingGenerators p).symm (v,s))) (Classical.propDecidable _) pass)
    have law := joint_nonce_deficit (I := HiddenIndex p) state visible pos first msg blocks flag c (publicRun visible) facts.valid Subtype.val_injective enough
      noOld away gate gate_to_base
      (fun s accepted => ⟨gated_blocks xs p v st.final s accepted,gated_reverse xs p v st.final s accepted⟩)
      (fun low row stored s accepted => gated_cached xs p v st.final s accepted low row.1 row.2 stored)
      after (fun _ => budget _) small ev
    exact transfer_seed (f := actual false visible) (g := actual true visible) (bad := fun s => ¬gate s) law
  have bound := deficit_bind_const vis (fun visible => seed >>= actual false visible) (fun visible => seed >>= actual true visible)
    ev _ (fun visible _ => paid visible)
  dsimp only
  unfold deficit mass at bound ⊢
  rw [←(order false).prEvent_eq (retained ev),←(order true).prEvent_eq (retained (fun a => ¬ev a))] at bound
  exact bound

end CommitGolfCandidate.Reconstruction.HidingTape
