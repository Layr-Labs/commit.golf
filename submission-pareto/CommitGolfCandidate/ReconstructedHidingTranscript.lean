import CommitGolfCandidate.NonceChainView
import CommitGolfCandidate.ReconstructedHidingView

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2048
local instance transcriptDiscrete {α : Type} : MeasurableSpace α := ⊤
noncomputable local instance transcriptKeys : SampleableType Generator.Key :=
  by classical exact SampleableType.ofFintype _
noncomputable local instance transcriptSalts : SampleableType PrivateSalts :=
  by classical exact SampleableType.ofFintype _

def widenTape (s : PrivateSalts) : CompleteSaltTape := fun i => (s i).setWidth 128

noncomputable def actualTape (π : Perm) (k : Generator.Key) : CompleteSaltTape :=
  widenTape (generatedSalts π k)

attribute [local irreducible] generatedSalts widenTape

noncomputable def sampledIndependent {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : TranscriptBuilder) (b : Bool) : ProbComp O := do
  let o ← Oracle.sample
  let ch ← fixedOracleRun o a.choose
  let r ← $ᵗ PrivateSalts
  observeTranscriptView a (pinnedHonestView build) o.compression ch b
    (BiPermutation.equiv Block o.permutation) (widenTape r)

noncomputable def sampledKeyed {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : TranscriptBuilder) (b : Bool) : ProbComp O := do
  let o ← Oracle.sample
  let ch ← fixedOracleRun o a.choose
  let k ← $ᵗ Generator.Key
  observeTranscriptView a (pinnedHonestView build) o.compression ch b (BiPermutation.equiv Block o.permutation) (actualTape o.permutation k)

theorem keyed_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : TranscriptBuilder) (b : Bool) :
    𝒟[sampledKeyed a build b] =
      𝒟[($ᵗ Compression) >>= fun c => keyedGame c (fun r => chainPublicComp a t build c b (widenTape r))] := by
  simp only [sampledKeyed,actualTape,Oracle.sample,bind_assoc,pure_bind,keyedGame]
  apply _root_.evalDist_bind_congr; intro c
  apply _root_.evalDist_bind_congr; intro π
  simp_rw [chain_comp_run a h build (⟨c,π⟩ : Oracle)]
  exact (distribution_bind_comm ($ᵗ Generator.Key) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm

theorem independent_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : TranscriptBuilder) (b : Bool) :
    𝒟[sampledIndependent a build b] =
      𝒟[($ᵗ Compression) >>= fun c => independentGame c (fun r => chainPublicComp a t build c b (widenTape r))] := by
  simp only [sampledIndependent,Oracle.sample,bind_assoc,pure_bind,independentGame]
  apply _root_.evalDist_bind_congr; intro c
  trans 𝒟[do let π ← $ᵗ Perm
             let r ← $ᵗ PrivateSalts
             fixedOracleRun ⟨c,π⟩ (chainPublicComp a t build c b (widenTape r))]
  · apply _root_.evalDist_bind_congr; intro π
    simp_rw [chain_comp_run a h build (⟨c,π⟩ : Oracle)]
    exact (distribution_bind_comm ($ᵗ PrivateSalts) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm
  · exact distribution_bind_comm _ _ _

theorem keyed_reference_distance {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : TranscriptBuilder) (b : Bool) :
    measureTVDist (sampledKeyed a build b) (sampledIndependent a build b) ≤
      generatorError (t+2*LENGTH+t) := by
  have d := measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression)
      (fun c => keyedGame c (fun r => chainPublicComp a t build c b (widenTape r)))
      (fun c => independentGame c (fun r => chainPublicComp a t build c b (widenTape r)))
      (δ := generatorError (t+2*LENGTH+t)) (by unfold generatorError;positivity)
      (fun c => generator_distance _ _ _ (fun r => chain_comp_bound a h build c b _))
  simpa only [measureTVDist,keyed_grouped a h build b,independent_grouped a h build b] using d

def KeyedTranscriptRefines (scheme : Scheme) (build : TranscriptBuilder) : Prop :=
  ∀ (o : Oracle) (m : Message) (p : Positions), fixedOracleRun o (executableTranscript scheme m p) =ᵈ
    (do let k ← $ᵗ Generator.Key
        pure (pinnedHonestView build o.compression (BiPermutation.equiv Block o.permutation) m p (actualTape o.permutation k)))

theorem executable_to_keyed {State Output : Type} {openingSize : Nat}
    (scheme : Scheme) (build : TranscriptBuilder) (refines : KeyedTranscriptRefines scheme build)
    (adversary : Hiding.HidingAdversary State Output openingSize) (which : Bool) :
    Hiding.runHiding (Hiding.hidingExperiment scheme adversary which) =ᵈ
      sampledKeyed adversary build which := by
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
  unfold sampledKeyed
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
  simp only [bind_assoc, pure_bind, observeTranscriptView, message]
  apply EvalDistEq.bind_right
  intro salts
  have equivalentOracle : fixedOracle oracle.compression (BiPermutation.equiv Block oracle.permutation) = oracle := by
    unfold fixedOracle
    rw [Equiv.symm_apply_apply]
  rw [equivalentOracle]

/-- An executable transcript refinement is sufficient for the exact two-stage
hiding clause of the challenge certificate. -/
theorem scheme_hiding_of_keyed (scheme : Scheme) (build : TranscriptBuilder)
    (refines : KeyedTranscriptRefines scheme build)
    (privacy : ∀ {State Output : Type} {openingSize budget : Nat}
      (adversary : Hiding.HidingAdversary State Output openingSize), Hiding.QueryBound adversary budget →
      measureTVDist (sampledKeyed adversary build false) (sampledKeyed adversary build true) ≤
        min 1 (((budget : ℝ)+1)/2^120)) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  constructor
  · intro _ budget
    positivity
  · intro openingSize budget _ State Output adversary bounded
    unfold measureTVDist
    rw [(executable_to_keyed scheme build refines adversary false).evalDist_eq,
      (executable_to_keyed scheme build refines adversary true).evalDist_eq]
    exact privacy adversary bounded

end CommitGolfCandidate.Reconstruction.HidingTape
