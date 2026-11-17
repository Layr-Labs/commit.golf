import CommitGolfCandidate.TwoPermutationHidingEager

/-! Exact remaining executable proof interface for the contract's hiding claim.
Any implementation refining the salted digest transcript inherits the result. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option exponentiation.threshold 2048

local instance bridgeDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

def executableTranscript (scheme : Scheme) (message : Message) (positions : Positions) :
    OracleComp World (Commitment × Proof) := do
  let (root, data) ← scheme.commit message
  let opening ← scheme.opening data positions
  pure (root, opening)

def TranscriptRefines (scheme : Scheme) (build : TranscriptBuilder) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions),
    fixedOracleRun oracle (executableTranscript scheme message positions) =ᵈ
      (do let salts ← sampleCompleteSaltTape
          pure (honestView build oracle.compression (BiPermutation.equiv Block oracle.permutation)
            message positions salts))

theorem packed_salt_tape_uniform {α : Type} (next : CompleteSaltTape → ProbComp α) :
    (($ᵗ BitVec (128 * LENGTH)) >>= fun packed => next (splitBlocks 128 LENGTH packed)) =ᵈ
      (sampleCompleteSaltTape >>= next) := by
  let split : BitVec (128 * LENGTH) → CompleteSaltTape := splitBlocks 128 LENGTH
  have bijective : Function.Bijective split := split_blocks_bijective 128 LENGTH (by decide)
  change (($ᵗ BitVec (128 * LENGTH)) >>= fun packed => next (split packed)) =ᵈ _
  rw [← bind_map_left]
  have transport := @SampleableType.map_uniformSample_evalDistEq_of_bijective
    (BitVec (128 * LENGTH)) CompleteSaltTape inferInstance completeSaltSampler split bijective
  exact transport.bind_left next

private theorem eager_fixed_handler (compress : Compression) (perm : Perm) {α : Type}
    (program : OracleComp World α) :
    eagerRun compress (BiPermutation.equiv Block perm) program = fixedOracleRun ⟨compress, perm⟩ program := by
  rw [fixed_run_eq_simulate, eagerRun]
  congr 1
  funext query
  rcases query with _ | (_ | (_ | _)) <;> rfl

noncomputable def sampledReference {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (which : Bool) : ProbComp Output := do
  let oracle ← Oracle.sample
  let challenge ← fixedOracleRun oracle adversary.choose
  let salts ← sampleCompleteSaltTape
  observeHonestView adversary build oracle.compression challenge which
    (BiPermutation.equiv Block oracle.permutation) salts

private theorem sampled_reference_eq {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (which : Bool) :
    sampledReference adversary build which =ᵈ
      (($ᵗ Compression) >>= fun compress => eagerFullReference adversary build compress which) := by
  unfold sampledReference Oracle.sample
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right ($ᵗ Compression)
  intro compress
  let : SampleableType (Completion (PermutationCache.empty Block).entries) :=
    (PermutationCache.empty Block).completionSampler
  let next (permutation : Perm) := do
    let challenge ← fixedOracleRun ⟨compress, permutation⟩ adversary.choose
    let salts ← sampleCompleteSaltTape
    observeHonestView adversary build compress challenge which (BiPermutation.equiv Block permutation) salts
  apply (uniform_transport_bind emptyTransport next).trans
  unfold eagerFullReference
  apply EvalDistEq.bind_right
  intro completion
  simp only [next, ← eager_fixed_handler, emptyTransport, Equiv.apply_symm_apply]
  rfl

theorem sampled_reference_hiding {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (budget : Nat) (bounded : Hiding.QueryBound adversary budget) :
    measureTVDist (sampledReference adversary build false) (sampledReference adversary build true) ≤
      min 1 (((budget : ℝ) + 1) / 2 ^ 120) := by
  unfold measureTVDist
  rw [(sampled_reference_eq adversary build false).evalDist_eq, (sampled_reference_eq adversary build true).evalDist_eq]
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
  intro compress
  exact eager_two_stage_hiding adversary build compress budget bounded

private theorem executable_to_reference {State Output : Type} {openingSize : Nat}
    (scheme : Scheme) (build : TranscriptBuilder) (refines : TranscriptRefines scheme build)
    (adversary : Hiding.HidingAdversary State Output openingSize) (which : Bool) :
    Hiding.runHiding (Hiding.hidingExperiment scheme adversary which) =ᵈ
      sampledReference adversary build which := by
  have grouping :
      Hiding.hidingExperiment scheme adversary which = (do
        let challenge ← adversary.choose
        let message := if which then challenge.message₁ else challenge.message₀
        let (root, proof) ← executableTranscript scheme message challenge.positions
        adversary.observe challenge.aux root proof) := by
    simp [Hiding.hidingExperiment, executableTranscript, bind_assoc]
  have counted :
      Hiding.runHiding (Hiding.hidingExperiment scheme adversary which) =
        (Oracle.sample >>= fun oracle => fixedOracleRun oracle (Hiding.hidingExperiment scheme adversary which)) := by
    simp only [Hiding.runHiding, fixedOracleRun, map_eq_bind_pure_comp, Function.comp_def]
  rw [counted]
  unfold sampledReference
  apply EvalDistEq.bind_right Oracle.sample
  intro oracle
  rw [grouping, fixed_oracle_run_bind]
  apply EvalDistEq.bind_right
  intro challenge
  rw [fixed_oracle_run_bind]
  let message := if which then challenge.message₁ else challenge.message₀
  apply ((refines oracle message challenge.positions).bind_left
    (fun (view : Commitment × Proof) => fixedOracleRun oracle
      (adversary.observe challenge.aux view.1 view.2))).trans
  simp only [bind_assoc, pure_bind, observeHonestView, message]
  apply EvalDistEq.bind_right
  intro salts
  have equivalentOracle : fixedOracle oracle.compression (BiPermutation.equiv Block oracle.permutation) = oracle := by
    unfold fixedOracle
    rw [Equiv.symm_apply_apply]
  rw [equivalentOracle]

/-- An executable transcript refinement is sufficient for the exact two-stage
hiding clause of the challenge certificate. -/
theorem scheme_hiding_of_transcript (scheme : Scheme) (build : TranscriptBuilder)
    (refines : TranscriptRefines scheme build) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  constructor
  · intro _ budget
    positivity
  · intro openingSize budget _ State Output adversary bounded
    unfold measureTVDist
    rw [(executable_to_reference scheme build refines adversary false).evalDist_eq,
      (executable_to_reference scheme build refines adversary true).evalDist_eq]
    exact sampled_reference_hiding adversary build budget bounded

end TwoPermutationPrototype.Sampling
