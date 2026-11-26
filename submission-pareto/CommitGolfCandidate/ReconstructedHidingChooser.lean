import CommitGolfCandidate.ReconstructedHidingLocalHigh
import CommitGolfCandidate.ReconstructedHidingFinalMargin

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingTraffic HidingReplay TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 2800000
set_option exponentiation.threshold 2048
set_option linter.constructorNameAsVariable false
attribute [local instance] jointFnSampler posteriorClosed posteriorOpen
attribute [local irreducible] pinnedCommonHigh pinnedFirstAddresses frameRestricted smoothBranch markedBranch frameHigh
local instance chooserDiscrete {α : Type} : MeasurableSpace α := ⊤

section Stage
variable {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n) (q : Nat) (build : TranscriptBuilder)
    (c : Compression) (ch : Hiding.HidingChallenge S n) (base : Cache)

noncomputable def restrictedStage (w : Bool) := do
  let v ← $ᵗ (VisibleGenerator ch.positions)
  let s ← $ᵗ (Secrets (ClosedIx ch.positions))
  frameRestricted a q build c ch base v s w

theorem restricted_stage_deficit (after : Nat) (cap : base.entries.length+3*LENGTH≤2^121)
    (small : after≤2^120) (budget : ∀ op ds, QueryBounded (guardedObserver a q build c ch op ds) after)
    (ev : O → Prop) :
    deficit (restrictedStage a q build c ch base false) (restrictedStage a q build c ch base true) ev ≤
      baseCost base.entries.length (2*LENGTH) + highCost ch.positions.card +
        combinedPostError (Fintype.card (HiddenIndex ch.positions)) after := by
  let p := ch.positions
  let vis := ($ᵗ (VisibleGenerator ch.positions))
  let secrets := ($ᵗ (Secrets (ClosedIx ch.positions)))
  let highs := fun v : VisibleGenerator p => pinnedCommonHigh base p ch.message₀ ch.message₁ (wideOpen v.1)
  let fail (v : VisibleGenerator p) := frameFail base p ch.message₀ ch.message₁ v
  let stage w (v : VisibleGenerator p) := secrets >>= fun s => frameRestricted a q build c ch base v s w
  let next w (v : VisibleGenerator p) (st : PinnedCommonHigh base) := secrets >>= fun s => frameHigh a q build c ch base v s w st
  let err := combinedPostError (Fintype.card (HiddenIndex p)) after
  have cardinality := hidden_index_count p
  rw [hiddenIndices,Finset.length_toList,Finset.card_univ] at cardinality
  have size : LENGTH=2^24 := rfl
  have room : base.entries.length+2*LENGTH+p.card≤2^121 := by omega
  have per (v : VisibleGenerator p) : deficit (stage false v) (stage true v) ev ≤ mass (highs v >>= fail v) (·=true)+err := by
    have bound := deficit_bind (highs v) (next false v) (next true v) ev (fail v) (·=true) err (fun st reached => by
      have highSame : highs v = pinnedCommonHigh base ch.positions ch.message₀ ch.message₁ (wideOpen v.1) := rfl
      have reach := (congrArg (fun d : ProbComp (PinnedCommonHigh base) => st∈support d) highSame).mp reached
      have cut := frame_high_deficit a q build c ch base v cap st reach after small (budget (wideOpen v.1)) ev
      have eq := detect_prob secrets (fun s => ¬jointGate (pinnedFirstAddresses ch.message₀ ch.message₁) p v st.final s)
      exact cut.trans_eq (congrArg (fun z : ENNReal => z.toReal+err) eq.symm))
    have law (w : Bool) := frame_high_order a q build c ch base v w room
    unfold deficit mass at bound ⊢
    rw [←(law false).prEvent_eq (retained ev),←(law true).prEvent_eq (retained (fun a => ¬ev a))] at bound
    exact bound
  have outer := deficit_bind vis (stage false) (stage true) ev (fun v => highs v >>= fail v) (·=true) err (fun v _ => per v)
  exact outer.trans (add_le_add (frame_gate_cost base p ch.message₀ ch.message₁ room) le_rfl)

theorem retained_stage_score (source : SampleableType (Key × GenReplies)) (w : Bool) (ev : O → Prop)
    (room : base.entries.length+3*LENGTH ≤ q+3*LENGTH) (cap : q+3*LENGTH≤2^121) :
    mass (restrictedStage a q build c ch base w) (retained ev) ≤
      mass ((@uniformSample _ source) >>= markedBranch a q build c w ch base) (retained ev) + (restrictedError q+honestCost) := by
  let p := ch.positions
  let vis := ($ᵗ (VisibleGenerator ch.positions))
  let secrets := ($ᵗ (Secrets (ClosedIx ch.positions)))
  let f (v : VisibleGenerator p) := fun s => frameRestricted a q build c ch base v s w
  let g (v : VisibleGenerator p) := fun s => markedBranch a q build c w ch base ((openingGenerators p).symm (v,s))
  have honestRoom : base.entries.length+2*LENGTH≤2^122 := by omega
  let pause := restrictedError q+honestCost
  have point (v : VisibleGenerator p) (s : Secrets (ClosedIx p)) : mass (f v s) (retained ev) ≤ mass (g v s) (retained ev)+pause := by
    let z := (openingGenerators p).symm (v,s)
    let smooth := smoothBranch a q build c w ch base z
    let : MeasurableSpace (O × Bool) := ⊤
    have dist := frame_smooth_near a q build c ch base v s w room cap
    have diff := (abs_sub_le_iff.mp (abs_prEvent_toReal_sub_le_measureTVDist (f v s) smooth (retained ev) Measurable.of_discrete)).1.trans dist
    have mark := smooth_branch_retained a q build c w ch base z ev honestRoom
    change mass (f v s) (retained ev) - mass smooth (retained ev) ≤ restrictedError q at diff
    change mass smooth (retained ev) ≤ mass (g v s) (retained ev)+honestCost at mark
    unfold pause
    linarith
  have inner (v : VisibleGenerator p) := real_bind_add secrets (f v) (g v) (retained ev) pause (fun s _ => point v s)
  have outer := real_bind_add vis (fun v => secrets >>= f v) (fun v => secrets >>= g v)
    (retained ev) pause (fun v _ => inner v)
  have order := @uniform_pair_reveal (Key × GenReplies) (VisibleGenerator p) (Secrets (ClosedIx p)) (O × Bool)
    source _ _ (openingGenerators p) (markedBranch a q build c w ch base)
  have same : mass (vis >>= fun v => secrets >>= g v) (retained ev) =
      mass ((@uniformSample _ source) >>= markedBranch a q build c w ch base) (retained ev) :=
    congrArg ENNReal.toReal (order.prEvent_eq (retained ev)).symm
  exact outer.trans_eq (congrArg (fun x => x+pause) same)

theorem chooser_deficit (source : SampleableType (Key × GenReplies)) (calls : Nat)
    (cached : base.entries.length≤calls) (used : calls≤q) (range : q+1≤2^120)
    (available : ∀ root proof, QueryBounded (a.observe ch.aux root proof) (q-calls))
    (ev : O → Prop) :
    let world := fun w => (@uniformSample _ source) >>= markedBranch a q build c w ch base
    deficit (world false) (world true) ev ≤ ((q:ℝ)+1)/2^120 := by
  let p := ch.positions
  have cardinality := hidden_index_count p
  rw [hiddenIndices,Finset.length_toList,Finset.card_univ] at cardinality
  have size : LENGTH = 2^24 := rfl
  have cap : q+3*LENGTH≤2^121 := by omega
  have room : base.entries.length+3*LENGTH≤q+3*LENGTH := by omega
  have observer (op : OpenedSalts p) (ds : DigestTape) : QueryBounded (guardedObserver a q build c ch op ds) (q-calls) := by
    have sufficient := fun root proof => PublicQueryBound.mono (available root proof) (Nat.sub_le q calls)
    unfold guardedObserver guardedView
    rw [ite_eq_left sufficient]
    exact available _ _
  have pair := restricted_stage_deficit a q build c ch base (q-calls) (room.trans cap) (by omega) observer ev
  have l := retained_stage_score a q build c ch base source false ev room cap
  have r := retained_stage_score a q build c ch base source true (fun x => ¬ev x) room cap
  have finalBound := joint_budget_margin base.entries.length (Fintype.card (HiddenIndex p)) p.card q calls cached used range
    (by omega) (by omega)
  dsimp only
  unfold deficit at pair ⊢
  linarith only [pair,l,r,finalBound]

end Stage
end CommitGolfCandidate.Reconstruction.HidingTape
