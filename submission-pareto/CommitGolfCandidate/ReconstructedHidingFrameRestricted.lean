import CommitGolfCandidate.ReconstructedHidingSmooth
import CommitGolfCandidate.ReconstructedHidingRestricted
import CommitGolfCandidate.ReconstructedHidingHighGate
import CommitGolfCandidate.ReconstructedHidingJointNonce

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingTraffic HidingReplay TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 2200000
set_option exponentiation.threshold 2048
attribute [local instance] jointFnSampler posteriorClosed
attribute [local irreducible] pinnedFirstAddresses hidingLeafDigests pinnedFullLeafDigests tapeFromReplies
local instance frameDiscrete {α : Type} : MeasurableSpace α := ⊤

open Classical in
noncomputable def frameFlag (base : Cache) (raw : List Reply) (p : Positions) (v : VisibleGenerator p) (s : Secrets (ClosedIx p)) : Bool :=
  decide (baseGood base raw ((openingGenerators p).symm (v,s)))

section Game
variable {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n) (q : Nat) (build : TranscriptBuilder)
    (c : Compression) (ch : Hiding.HidingChallenge S n) (base : Cache)
    (v : VisibleGenerator ch.positions) (s : Secrets (ClosedIx ch.positions))

noncomputable def frameObserve : DigestTape → BiPermutation Block → ProbComp (O × Bool) :=
  smoothObserve a q build c ch (wideOpen v.1) (genPermit s.1.1 (proposedReplies (knownBlocks ch.positions v.1 v.2) s))
    (frameFlag base (pinnedFirstAddresses ch.message₀ ch.message₁) ch.positions v s)

noncomputable def frameRestricted (w : Bool) :=
  pinnedClosedRestrictedWorld base ch.positions ch.message₀ ch.message₁ (wideOpen v.1) (wideClosed s.1.2) w
    (frameObserve a q build c ch base v s)

theorem frame_smooth_near (w : Bool) (room : base.entries.length+3*LENGTH≤q+3*LENGTH) (cap : q+3*LENGTH≤2^121) :
    @measureTVDist ProbComp (O × Bool) _ ⊤ (frameRestricted a q build c ch base v s w)
      (smoothBranch a q build c w ch base ((openingGenerators ch.positions).symm (v,s))) ≤ restrictedError q := by
  let op := wideOpen v.1
  let cl := wideClosed s.1.2
  let obs := frameObserve a q build c ch base v s
  have agree (i : Index) (present : i∈ch.positions) : ch.message₀ i=ch.message₁ i := congrFun ch.agree ⟨i,present⟩
  have est := pinned_closed_restricted_world_near base ch.positions ch.message₀ ch.message₁ op cl w agree obs
    (q+3*LENGTH) room cap (fun result reached => by
      obtain ⟨length,_,covered⟩ := pinned_full_const_frame base [] (pinnedFirstAddresses ch.message₀ ch.message₁) result reached
      rw [pinned_first_addresses_length] at length
      exact ⟨length,covered⟩)
  let r := widenTape (joinSalts ch.positions v.1 s.1.2)
  let z := (openingGenerators ch.positions).symm (v,s)
  have salts : tapeFromReplies z.2 = joinSalts ch.positions v.1 s.1.2 := opening_salts ch.positions v s
  have opened : (fun i : OpenIx ch.positions => r i.val) = op := by
    funext i
    exact congrArg (fun t : Salt => t.setWidth 128) (dite_eq_left i.property)
  have law : (base.sample >>= fun p => obs
      (hidingLeafDigests p.val (if w then ch.message₁ else ch.message₀) (mergeSaltTape op cl)) p.val) =
      smoothBranch a q build c w ch base z := by
    unfold smoothBranch
    apply bind_congr
    intro p
    have same := congrArg (hidingLeafDigests p.val (if w then ch.message₁ else ch.message₀)) (wide_merge ch.positions v.1 s.1.2)
    rw [same,honest_masked_tape,salts]
    exact (congrArg (fun opening => smoothObserve a q build c ch opening (genPermit z.1 z.2)
      (frameFlag base (pinnedFirstAddresses ch.message₀ ch.message₁) ch.positions v s)
      (pinnedFullLeafDigests p.val (if w then ch.message₁ else ch.message₀) r) p.val) opened).symm
  rw [law] at est
  simpa only [frameRestricted,restrictedError,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using est

noncomputable def frameAfter (w : Bool) (upper : Block → BitVec 1344) (table : Cache) :=
  afterHiddenSampler table ch.positions (pure (wideClosed s.1.2)) ch.message₀ ch.message₁
    (wideOpen v.1) w upper (frameObserve a q build c ch base v s)

noncomputable def frameHigh (w : Bool) (st : PinnedCommonHigh base) := do
  let draws ← samplePinnedLows (2*LENGTH+ch.positions.card)
  frameAfter a q build c ch base v s w (pinnedBoundedHigh (pinnedFirstAddresses ch.message₀ ch.message₁) st.first.zero)
    (st.final.realize (pinnedPlaceLows (fun _ => 0) 0 draws))

theorem frame_high_order (w : Bool) (room : base.entries.length+2*LENGTH+ch.positions.card≤2^121) :
    (($ᵗ (Secrets (ClosedIx ch.positions))) >>= fun sec => frameRestricted a q build c ch base v sec w) =ᵈ
      (pinnedCommonHigh base ch.positions ch.message₀ ch.message₁ (wideOpen v.1) >>= fun st =>
        ($ᵗ (Secrets (ClosedIx ch.positions))) >>= fun sec => frameHigh a q build c ch base v sec w st) := by
  let seeds := ($ᵗ (Secrets (ClosedIx ch.positions)))
  let highs := pinnedCommonHigh base ch.positions ch.message₀ ch.message₁ (wideOpen v.1)
  let after := fun (sec : Secrets (ClosedIx ch.positions)) (st : PinnedCommonHigh base) => frameHigh a q build c ch base v sec w st
  trans (seeds >>= fun sec => highs >>= after sec)
  · apply EvalDistEq.bind_right
    intro sec
    have eq := pinned_common_full_separates base ch.positions ch.message₀ ch.message₁ (wideOpen v.1) room
      (frameAfter a q build c ch base v sec w)
    unfold frameAfter afterHiddenSampler at eq
    simp only [pure_bind] at eq
    exact eq
  · exact EvalDistEq.of_evalDist_eq (distribution_bind_comm seeds highs after)

end Game
end CommitGolfCandidate.Reconstruction.HidingTape
