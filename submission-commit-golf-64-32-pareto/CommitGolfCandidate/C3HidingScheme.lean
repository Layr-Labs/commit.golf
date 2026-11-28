import CommitGolfCandidate.C3HidingEager

/-! The contract's hiding clause for the 3c1p transcript: split off the compression function,
then apply `c3_final_reference_hiding` for every fixed compression function. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 650000
set_option exponentiation.threshold 2048
set_option autoImplicit false

local instance c3SchemeDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

theorem c3_sampled_reference_eq {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (which : Bool) :
    sampledReferenceView adversary (c3HonestView build) which =ᵈ
      (($ᵗ Compression) >>= fun compress => c3ViewReference adversary build compress which) := by
  unfold sampledReferenceView Oracle.sample
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right ($ᵗ Compression)
  intro compress
  let : SampleableType (Completion (PermutationCache.empty Block).entries) :=
    (PermutationCache.empty Block).completionSampler
  let next (permutation : Perm) := do
    let challenge ← fixedOracleRun ⟨compress, permutation⟩ adversary.choose
    let salts ← sampleCompleteSaltTape
    observeTranscriptView adversary (c3HonestView build) compress challenge which
      (BiPermutation.equiv Block permutation) salts
  apply (uniform_transport_bind emptyTransport next).trans
  unfold c3ViewReference
  apply EvalDistEq.bind_right
  intro completion
  simp only [next, ← eager_fixed_handler, emptyTransport, Equiv.apply_symm_apply]
  rfl

/-- The contract's hiding clause for any scheme whose executable transcript is the honest
3c1p transcript built by `build`. -/
theorem scheme_hiding_of_c3_transcript (scheme : Scheme) (build : TranscriptBuilder)
    (refines : C3TranscriptRefines scheme build) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  apply scheme_hiding_of_transcript_view scheme (c3HonestView build) refines
  intro State Output openingSize adversary budget bounded
  unfold measureTVDist
  rw [(c3_sampled_reference_eq adversary build false).evalDist_eq,
    (c3_sampled_reference_eq adversary build true).evalDist_eq]
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
  intro compress
  exact c3_final_reference_hiding adversary build compress budget bounded

end TwoPermutationPrototype.Sampling
