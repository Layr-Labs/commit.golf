import CommitGolfCandidate.MirrorHidingEager

/-! # Hiding for a mirrored leaf: the contract's clause

Split off the compression function, then apply `final_reference_hiding` for every fixed
compression function. `scheme_hiding_of_mirror_transcript` holds for every `MirrorLayout` and
every scheme whose executable transcript is `mirrorView` of a uniform salt tape. -/
namespace TwoPermutationPrototype.Sampling.Mirror
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 650000
set_option exponentiation.threshold 2048
set_option autoImplicit false

local instance schemeDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

variable (Λ : MirrorLayout)

theorem sampled_reference_eq {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (which : Bool) :
    sampledReferenceView adversary (mirrorView Λ build) which =ᵈ
      (($ᵗ Compression) >>= fun compress => viewReference Λ adversary build compress which) := by
  unfold sampledReferenceView Oracle.sample
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right ($ᵗ Compression)
  intro compress
  let : SampleableType (Completion (PermutationCache.empty Block).entries) :=
    (PermutationCache.empty Block).completionSampler
  let next (permutation : Perm) := do
    let challenge ← fixedOracleRun ⟨compress, permutation⟩ adversary.choose
    let salts ← sampleCompleteSaltTape
    observeTranscriptView adversary (mirrorView Λ build) compress challenge which
      (BiPermutation.equiv Block permutation) salts
  apply (uniform_transport_bind emptyTransport next).trans
  unfold viewReference
  apply EvalDistEq.bind_right
  intro completion
  simp only [next, ← eager_fixed_handler, emptyTransport, Equiv.apply_symm_apply]
  rfl

/-- **The contract's hiding clause for a mirrored one-call leaf.** -/
theorem scheme_hiding_of_mirror_transcript (scheme : Scheme) (build : TranscriptBuilder)
    (refines : TranscriptRefinesView scheme (mirrorView Λ build)) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  apply scheme_hiding_of_transcript_view scheme (mirrorView Λ build) refines
  intro State Output openingSize adversary budget bounded
  unfold measureTVDist
  rw [(sampled_reference_eq Λ adversary build false).evalDist_eq,
    (sampled_reference_eq Λ adversary build true).evalDist_eq]
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
  intro compress
  exact final_reference_hiding Λ adversary build compress budget bounded

end TwoPermutationPrototype.Sampling.Mirror
