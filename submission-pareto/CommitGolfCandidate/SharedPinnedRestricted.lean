import CommitGolfCandidate.TaggedPinnedRestrictedWorld
import CommitGolfCandidate.SharedPinnedConditional

/-! Restricted-world hiding with a shared nonce tape and split query budgets. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048
attribute [local irreducible] pinnedFirstAddresses pinnedCommonHigh
local instance SharedPinnedRestrictedDiscrete {α : Type} : MeasurableSpace α := ⊤

private theorem shared_world_after_exposure {α : Type} {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed] (valid : state.high.Valid count)
    (positions : Positions) (left right : Message) (opened : OpenedSalts positions) (upper : Block → BitVec 1344)
    (seen : ∀ i : {i : Index // i ∈ positions}, pinnedPublicAddress left upper i.val (opened i) ∈ state.opened)
    (away : ∀ message nonce address, address ∈ pinnedHiddenAddresses positions message upper nonce →
        address ∉ state.opened)
    (hiddenRoom : state.high.zero.entries.length + Fintype.card (HiddenIndex positions) ≤ 2^121)
    (sites : Fintype.card (HiddenIndex positions) ≤ 2^24)
    (compress : Compression) (observer : DigestTape → OracleComp World α)
    (before after : Nat) (bounded : ∀ digest, QueryBounded (observer digest) after) (preBound : base.entries.length ≤ before) :
    let observe := fun digest p => fixedOracleRun (fixedOracle compress p) (observer digest)
    let resumed := fun which cache => pinnedRestrictedAfterCommon cache positions left right opened which upper observe
    measureTVDist
      (samplePinnedLows count >>= fun draws =>
        resumed false (state.high.realize (pinnedPlaceLows (fun _ => 0) 0 draws)))
      (samplePinnedLows count >>= fun draws =>
        resumed true (state.high.realize (pinnedPlaceLows (fun _ => 0) 0 draws))) ≤ sharedPinnedCharge before after := by
  let observe := fun digest p => fixedOracleRun (fixedOracle compress p) (observer digest)
  let resumed (which : Bool) (cache : Cache) :=
    pinnedRestrictedAfterCommon cache positions left right opened which upper observe
  have f₀ := pinned_opened_lows_equivalence state (resumed false)
  have f₁ := pinned_opened_lows_equivalence state (resumed true)
  change measureTVDist
    (samplePinnedLows count >>= fun draws =>
      resumed false (state.high.realize (pinnedPlaceLows (fun _ => 0) 0 draws)))
    (samplePinnedLows count >>= fun draws =>
      resumed true (state.high.realize (pinnedPlaceLows (fun _ => 0) 0 draws))) ≤ _
  unfold measureTVDist
  rw [f₀.evalDist_eq, f₁.evalDist_eq]
  change measureTVDist (_ >>= _) (_ >>= _) ≤ _
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by unfold sharedPinnedCharge; positivity)
  intro visible
  have l₀ := pinned_visible_observer_equivalence state positions left right opened false upper visible seen observe
  have l₁ := pinned_visible_observer_equivalence state positions left right opened true upper visible seen observe
  change measureTVDist (samplePinnedLowFn state.PrivateSlot >>= fun privateLow =>
    pinnedRestrictedAfterCommon (state.high.realize (pinnedFinLowTape (state.merge visible privateLow)))
      positions left right opened false upper observe)
    (samplePinnedLowFn state.PrivateSlot >>= fun privateLow =>
      pinnedRestrictedAfterCommon (state.high.realize (pinnedFinLowTape (state.merge visible privateLow)))
        positions left right opened true upper observe) ≤ _
  unfold measureTVDist
  rw [l₀.evalDist_eq, l₁.evalDist_eq]
  let observePublic (digest : UnopenedDigestTape positions) :=
    observer (fullDigestTape (pinnedOpenedDigestTape left upper opened (state.publicReply visible)) digest)
  let runPublic := fun digest p => fixedOracleRun (fixedOracle compress p) (observePublic digest)
  exact shared_conditional_distance state valid visible Subtype.val Subtype.val_injective
    (fun w => pinnedHiddenFirst positions (if w then right else left) upper)
    (fun w i => messageWords (if w then right else left) i.val) hiddenRoom
    (fun w => away (if w then right else left)) compress observePublic before after
    (fun _ => bounded _) preBound sites

theorem shared_restricted_two_world {α : Type} (base : Cache) (positions : Positions)
    (left right : Message) (opened : OpenedSalts positions)
    (compress : Compression) (observer : DigestTape → OracleComp World α)
    (before after : Nat) (bounded : ∀ digest, QueryBounded (observer digest) after)
    (preBound : base.entries.length ≤ before) (room : base.entries.length + 3 * LENGTH ≤ 2^121) :
    let observe := fun digest p => fixedOracleRun (fixedOracle compress p) (observer digest)
    measureTVDist (pinnedRestrictedWorld base positions left right opened false observe)
      (pinnedRestrictedWorld base positions left right opened true observe) ≤ sharedPinnedCharge before after := by
  classical
  let observe := fun digest p => fixedOracleRun (fixedOracle compress p) (observer digest)
  have nonneg : 0 ≤ sharedPinnedCharge before after := by unfold sharedPinnedCharge; positivity
  have cardinality : Fintype.card (HiddenIndex positions) + positions.card = LENGTH := by
    have exactCount := hidden_index_count positions
    rw [hiddenIndices, Finset.length_toList, Finset.card_univ] at exactCount
    exact exactCount
  have prepRoom : base.entries.length + 2*LENGTH + positions.card ≤ 2^121 := by omega
  have e₀ := pinned_common_full_separates base positions left right opened prepRoom
    (fun upper seeded => pinnedRestrictedAfterCommon seeded positions left right opened false upper observe)
  have e₁ := pinned_common_full_separates base positions left right opened prepRoom
    (fun upper seeded => pinnedRestrictedAfterCommon seeded positions left right opened true upper observe)
  change measureTVDist (pinnedRestrictedWorld base positions left right opened false observe)
    (pinnedRestrictedWorld base positions left right opened true observe) ≤ _
  unfold pinnedRestrictedWorld measureTVDist
  rw [e₀.evalDist_eq, e₁.evalDist_eq]
  let finish (which : Bool) (common : PinnedCommonHigh base) : ProbComp α := do
    let draws ← samplePinnedLows (2 * LENGTH + positions.card)
    pinnedRestrictedAfterCommon (common.final.realize (pinnedPlaceLows (fun _ => 0) 0 draws))
      positions left right opened which (pinnedBoundedHigh (pinnedFirstAddresses left right) common.first.zero) observe
  change measureTVDist (pinnedCommonHigh base positions left right opened >>= finish false)
    (pinnedCommonHigh base positions left right opened >>= finish true) ≤ _
  refine pinned_restricted_bind_support_le (pinnedCommonHigh base positions left right opened)
    (finish false) (finish true) _ nonneg ?_
  intro common reached
  have facts := pinned_common_high_facts base positions left right opened prepRoom common reached
  let state := PinnedCommonHigh.openedState facts
  let upper := pinnedBoundedHigh (pinnedFirstAddresses left right) common.first.zero
  have hiddenRoom : state.high.zero.entries.length + Fintype.card (HiddenIndex positions) ≤ 2^121 := by
    have size := facts.tableBound
    change state.high.zero.entries.length ≤ _ at size
    omega
  have sites : Fintype.card (HiddenIndex positions) ≤ 2^24 := by
    have : LENGTH = 2^24 := rfl
    omega
  have openMatches : pinnedOpenedAddresses positions left upper opened = state.opened := by
    rw [show state.opened = common.opened from rfl, facts.openedShape]
    apply pinned_bound_high_opened
    intro i _
    exact pinned_first_address_mem left right false i
  have seen (i : {i : Index // i ∈ positions}) :
      pinnedPublicAddress left upper i.val (opened i) ∈ state.opened := by
    rw [← openMatches]
    have member := Finset.mem_toList.mpr i.property
    refine List.mem_map.mpr ⟨i.val, member, ?_⟩
    simp only [publicOpenedSalts, dite_eq_left i.property]
  have away (message : Message) (nonce : UnopenedSalts positions) (address : Block)
      (included : address ∈ pinnedHiddenAddresses positions message upper nonce) :
      address ∉ state.opened := by
    rw [← openMatches]
    exact pinned_hidden_addresses_away left message upper upper opened nonce address included
  exact shared_world_after_exposure state facts.valid positions left right opened upper seen away hiddenRoom sites
    compress observer before after bounded preBound

end TwoPermutationPrototype.Sampling
