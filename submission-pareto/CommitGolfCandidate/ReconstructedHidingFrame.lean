import CommitGolfCandidate.ReconstructedHidingPrefix
import CommitGolfCandidate.ReconstructedHidingJointObserver
import CommitGolfCandidate.ReconstructedHidingOpenings

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingReplay HidingTraffic TwoPermutationPrototype.Sampling
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048
attribute [local instance] jointFnSampler

abbrev VisibleGenerator (p : Finset Position) := (OpenIx p → Salt) × Slack

private def groupOpening {K V H T R : Type} : (K × (V × H × T × R)) ≃ ((V × T) × ((K × H) × R)) where
  toFun x := ((x.2.1,x.2.2.2.1),((x.1,x.2.2.1),x.2.2.2.2))
  invFun x := (x.2.1.1,x.1.1,x.2.1.2,x.1.2,x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def openingGenerators (p : Finset Position) :
    (Key × GenReplies) ≃ (VisibleGenerator p × Secrets (ClosedIx p)) :=
  (((Equiv.refl Key).prodCongr (repliesByGroup.trans (splitOpening p))).trans groupOpening)

theorem opening_key_replies (p : Finset Position) (v : VisibleGenerator p) (s : Secrets (ClosedIx p)) :
    (openingGenerators p).symm (v,s) = (s.1.1,proposedReplies (knownBlocks p v.1 v.2) s) := rfl

theorem opening_salts (p : Finset Position) (v : VisibleGenerator p) (s : Secrets (ClosedIx p)) :
    tapeFromReplies (proposedReplies (knownBlocks p v.1 v.2) s) = joinSalts p v.1 s.1.2 := by
  have e := congrArg (fun z : VisibleGenerator p × Secrets (ClosedIx p) =>
      joinSalts p z.1.1 z.2.1.2) ((openingGenerators p).apply_symm_apply (v,s))
  let y := proposedReplies (knownBlocks p v.1 v.2) s
  change joinSalts p (fun i => tapeFromReplies y i.val) (fun i => tapeFromReplies y i.val) = _ at e
  exact ((openClose p).symm_apply_apply (tapeFromReplies y)).symm.trans e

theorem opening_blocks (p : Finset Position) (v : VisibleGenerator p) (s : Secrets (ClosedIx p)) (j : Fin groupCount) :
    (blockSplit (proposedReplies (knownBlocks p v.1 v.2) s j)).1 = knownBlocks p v.1 v.2 s.1.2 (groupIndex j) :=
  congrArg Prod.fst (blockSplit.apply_symm_apply _)

theorem opening_sample {A : Type} (p : Finset Position) (f : (Key × GenReplies) → ProbComp A) :
    (($ᵗ (Key × GenReplies)) >>= f) =ᵈ
      (do let v ← $ᵗ (VisibleGenerator p)
          let s ← $ᵗ (Secrets (ClosedIx p))
          f (s.1.1,proposedReplies (knownBlocks p v.1 v.2) s)) := by
  let transport := transportOfEquiv (openingGenerators p)
  apply (uniform_transport_bind transport f).trans
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc,pure_bind]
  exact EvalDistEq.refl _

end CommitGolfCandidate.Reconstruction.HidingTape
