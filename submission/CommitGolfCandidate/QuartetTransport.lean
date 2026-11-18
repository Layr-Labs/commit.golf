import CommitGolfCandidate.QuartetRestricted
import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.K3GQModel

namespace TwoPermutationPrototype.Sampling.Quartet
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 650000
set_option exponentiation.threshold 2048

local instance pinnedTransportDiscreteSpace {α : Type} : MeasurableSpace α := ⊤


/-- The quartet lookup takes the group index: the node truncation depends on its parity. -/
abbrev QuartetBuilder := (Nat → BitVec 1024 → BitVec 256) → TranscriptBuilder

/-- The node of quartet group `g` with payload `payload` (window `0^72 ‖ d0 d1 d2 d3`). -/
def quartetLookup (p : BiPermutation Block) (group : Nat) (payload : BitVec 1024) : BitVec 256 :=
  quartetNode group (p.forward (quartetEncode payload))

theorem quartet_lookup_stable (p p' : BiPermutation Block)
    (same : ∀ x ∈ quartetDomain, p.forward x = p'.forward x) : quartetLookup p = quartetLookup p' := by
  classical
  funext group payload
  unfold quartetLookup
  exact congrArg (quartetNode group) (same _ (List.mem_map.mpr ⟨payload, by simp, rfl⟩))

def honestView (build : QuartetBuilder) (compress : Compression) (p : BiPermutation Block)
    (message : Message) (positions : Positions) (salts : CompleteSaltTape) : Commitment × Proof :=
  build (quartetLookup p) compress positions (fun index => salts index.val) (pinnedFullLeafDigests p message salts)

abbrev QuartetRefines (s : Scheme) (build : QuartetBuilder) := TranscriptRefinesView s (honestView build)

noncomputable def viewReference {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : QuartetBuilder)
    (compress : Compression) (which : Bool) : ProbComp Output := do
  let permutation ← (PermutationCache.empty Block).sample
  let challenge ← eagerRun compress permutation.val adversary.choose
  let salts ← sampleCompleteSaltTape
  observeTranscriptView adversary (honestView build) compress challenge which permutation.val salts

theorem sampled_reference_eq {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : QuartetBuilder)
    (which : Bool) :
    sampledReferenceView adversary (honestView build) which =ᵈ
      (($ᵗ Compression) >>= fun compress => viewReference adversary build compress which) := by
  unfold sampledReferenceView Oracle.sample
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right ($ᵗ Compression)
  intro compress
  let : SampleableType (Completion (PermutationCache.empty Block).entries) :=
    (PermutationCache.empty Block).completionSampler
  let next (permutation : Perm) := do
    let challenge ← fixedOracleRun ⟨compress, permutation⟩ adversary.choose
    let salts ← sampleCompleteSaltTape
    observeTranscriptView adversary (honestView build) compress challenge which
      (BiPermutation.equiv Block permutation) salts
  apply (uniform_transport_bind emptyTransport next).trans
  unfold viewReference
  apply EvalDistEq.bind_right
  intro completion
  simp only [next, ← eager_fixed_handler, emptyTransport, Equiv.apply_symm_apply]
  rfl

theorem scheme_hiding_of_transcript (scheme : Scheme) (build : QuartetBuilder)
    (refines : QuartetRefines scheme build)
    (referenceBound : ∀ {State Output : Type} {openingSize : Nat}
      (adversary : Hiding.HidingAdversary State Output openingSize) (compress : Compression) (budget : Nat),
      Hiding.QueryBound adversary budget →
      measureTVDist (viewReference adversary build compress false)
        (viewReference adversary build compress true) ≤ min 1 (((budget : ℝ) + 1) / 2 ^ 120)) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  apply scheme_hiding_of_transcript_view scheme (honestView build) refines
  intro State Output openingSize adversary budget bounded
  unfold measureTVDist
  rw [(sampled_reference_eq adversary build false).evalDist_eq,
    (sampled_reference_eq adversary build true).evalDist_eq]
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
  intro compress
  exact referenceBound adversary compress budget bounded

end TwoPermutationPrototype.Sampling.Quartet
