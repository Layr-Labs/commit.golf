import CommitGolfCandidate.ReconstructedHidingFrameRestricted

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingTraffic HidingReplay TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 2200000
set_option exponentiation.threshold 2048
attribute [local instance] jointFnSampler posteriorClosed posteriorOpen
attribute [local irreducible] pinnedFirstAddresses pinnedCommonHigh blockSplit
local instance gateDiscrete {α : Type} : MeasurableSpace α := ⊤

open Classical in
noncomputable def detect {A : Type} (d : ProbComp A) (event : A → Prop) : ProbComp Bool :=
  (fun a => decide (event a)) <$> d

theorem detect_prob {A : Type} (d : ProbComp A) (event : A → Prop) :
    Pr{let b ← detect d event}[b=true] = Pr{let a ← d}[event a] := by
  classical
  rw [detect,prEvent_map]
  apply congrArg (fun p : A → Prop => Pr{let a ← d}[p a])
  funext a
  exact propext (decide_eq_true_iff)

noncomputable def frameFail (base : Cache) (p : Positions) (left right : Message) (v : VisibleGenerator p)
    (st : PinnedCommonHigh base) :=
  detect ($ᵗ (Secrets (ClosedIx p))) (fun s => ¬jointGate (pinnedFirstAddresses left right) p v st.final s)

noncomputable def highCost (openingSize : Nat) : ℝ :=
  (groupCount:ℝ)*((2*LENGTH:ℝ)/2^359)+(groupCount:ℝ)*(openingSize/2^359)

theorem uniform_pair_reveal {X V S A : Type} [SampleableType X] [SampleableType V] [SampleableType S]
    (e : X ≃ V × S) (f : X → ProbComp A) :
    (($ᵗ X) >>= f) =ᵈ (do let v ← $ᵗ V; let s ← $ᵗ S; f (e.symm (v,s))) := by
  apply (uniform_transport_bind (transportOfEquiv e) f).trans
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc,pure_bind]
  exact EvalDistEq.refl _

theorem frame_gate_cost (base : Cache) (p : Positions) (left right : Message)
    (room : base.entries.length+2*LENGTH+p.card≤2^121) :
    mass (do let v ← $ᵗ (VisibleGenerator p)
             let st ← pinnedCommonHigh base p left right (wideOpen v.1)
             frameFail base p left right v st) (·=true) ≤
      baseCost base.entries.length (2*LENGTH) + highCost p.card := by
  classical
  let raw := pinnedFirstAddresses left right
  let orig := ($ᵗ (Key × GenReplies))
  let vis := ($ᵗ (VisibleGenerator p))
  let secrets := ($ᵗ (Secrets (ClosedIx p)))
  let hi := fun v : VisibleGenerator p => pinnedCommonHigh base p left right (wideOpen v.1)
  let test (v : VisibleGenerator p) (s : Secrets (ClosedIx p)) (st : PinnedCommonHigh base) :=
    (pure (@decide (¬jointGate raw p v st.final s) (Classical.propDecidable _)) : ProbComp Bool)
  let score (z : Key × GenReplies) :=
    let vz := (openingGenerators p) z
    hi vz.1 >>= test vz.1 vz.2
  have order : (do let v ← vis; let st ← hi v; frameFail base p left right v st) =ᵈ (orig >>= score) := by
    apply EvalDistEq.trans _ (uniform_pair_reveal (openingGenerators p) score).symm
    apply EvalDistEq.bind_right vis
    intro v
    trans (secrets >>= fun s => hi v >>= test v s)
    · change (hi v >>= fun st => (fun s => @decide (¬jointGate raw p v st.final s) (Classical.propDecidable _)) <$> secrets) =ᵈ _
      simp only [map_eq_bind_pure_comp,Function.comp_def]
      exact EvalDistEq.of_evalDist_eq (distribution_bind_comm secrets (hi v) (fun s st => test v s st)).symm
    · apply EvalDistEq.bind_right secrets
      intro s
      simp only [score,Equiv.apply_symm_apply]
      exact EvalDistEq.refl _
  let miss := fun z : Key × GenReplies => ¬baseGood base raw z
  let upper := (groupCount:ENNReal)*((2*LENGTH:ENNReal)/2^359)+(groupCount:ENNReal)*(p.card/2^359)
  have each (z : Key × GenReplies) (_ : z∈support orig) (clean : ¬miss z) :
      Pr{let b ← score z}[b=true] ≤ upper := by
    let v := ((openingGenerators p) z).1
    let s := ((openingGenerators p) z).2
    let B := knownBlocks p v.1 v.2 s.1.2
    have old : baseGood base raw ((openingGenerators p).symm (v,s)) := by
      have restore : (openingGenerators p).symm (v,s)=z := (openingGenerators p).symm_apply_apply z
      rw [restore]
      exact Classical.not_not.mp clean
    have high := new_high_cost base p left right (wideOpen v.1) room B
    have card : Fintype.card Group=groupCount := by simp [Group,Fintype.card_prod,groupCount]
    rw [card] at high
    have eq : score z = (fun st => @decide (¬jointGate raw p v st.final s) (Classical.propDecidable _)) <$> hi v :=
      bind_pure_comp _ _
    rw [eq,prEvent_map]
    refine (prEvent_mono (hi v) _ _ ?_).trans high
    intro st excluded
    have nogate : ¬jointGate raw p v st.final s := @of_decide_eq_true (¬jointGate raw p v st.final s) (Classical.propDecidable _) excluded
    exact Classical.not_not.mp (fun none => nogate ⟨old,none⟩)
  have cut := prEvent_bind_le_prEvent_add_of_support orig score miss (·=true) each
  have inequality := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _,by unfold upper; finiteness⟩) cut
  rw [ENNReal.toReal_add (prEvent_ne_top _) (by unfold upper; finiteness)] at inequality
  have cost : upper.toReal=highCost p.card := by
    unfold upper highCost
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_natCast]
  rw [cost] at inequality
  unfold mass
  rw [order.prEvent_eq (·=true)]
  have prior := base_cost_bound base raw
  have costs := congrArg (baseCost base.entries.length) (pinned_first_addresses_length left right)
  exact inequality.trans (add_le_add (prior.trans_eq costs) le_rfl)

end CommitGolfCandidate.Reconstruction.HidingTape
