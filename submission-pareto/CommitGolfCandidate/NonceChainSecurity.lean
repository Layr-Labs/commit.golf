import CommitGolfCandidate.NonceChainView
import CommitGolfCandidate.SharedPinnedFinal

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces chain_budget)
local instance chainSecurityDiscrete {α : Type} : MeasurableSpace α := ⊤

/-- The honest salts: generator outputs with their top six bits cleared. -/
noncomputable def maskedNonces (π : Perm) (k : Key) : SaltArray := fun i => maskSalt (actualNonces π k i)

noncomputable def sampledChain {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : TranscriptBuilder) (b : Bool) : ProbComp O := do
  let o ← Oracle.sample
  let ch ← fixedOracleRun o a.choose
  let k ← $ᵗ Key
  observeTranscriptView a (pinnedHonestView build) o.compression ch b (BiPermutation.equiv Block o.permutation) (maskedNonces o.permutation k)

theorem chain_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : TranscriptBuilder) (b : Bool) :
    𝒟[sampledChain a build b] =
      𝒟[($ᵗ Compression) >>= fun c => chainNonceGame c (fun r => chainPublicComp a t build c b (fun i => maskSalt (r i)))] := by
  simp only [sampledChain,maskedNonces,Oracle.sample,bind_assoc,pure_bind,chainNonceGame]
  apply _root_.evalDist_bind_congr; intro c
  apply _root_.evalDist_bind_congr; intro π
  simp_rw [chain_comp_run a h build (⟨c,π⟩ : Oracle)]
  exact (distribution_bind_comm ($ᵗ Key) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm

theorem iid_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : TranscriptBuilder) (b : Bool) :
    𝒟[sampledReferenceView a (pinnedMaskedView (maskBuild build)) b] =
      𝒟[($ᵗ Compression) >>= fun c => iidNonceGame c (fun r => chainPublicComp a t build c b (fun i => maskSalt (r i)))] := by
  simp only [sampledReferenceView,Oracle.sample,bind_assoc,pure_bind,iidNonceGame]
  apply _root_.evalDist_bind_congr; intro c
  trans 𝒟[do let π ← $ᵗ Perm
             let r ← $ᵗ SaltArray
             fixedOracleRun ⟨c,π⟩ (chainPublicComp a t build c b (fun i => maskSalt (r i)))]
  · apply _root_.evalDist_bind_congr; intro π
    simp_rw [chain_comp_run a h build (⟨c,π⟩ : Oracle)]
    exact (distribution_bind_comm ($ᵗ SaltArray) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm
  · exact distribution_bind_comm _ _ _

theorem chain_reference_hiding {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : TranscriptBuilder) :
    measureTVDist (sampledChain a build false) (sampledChain a build true) ≤ min 1 (((t : ℝ)+1)/2^120) := by
  have side (b : Bool) :
      measureTVDist (sampledChain a build b) (sampledReferenceView a (pinnedMaskedView (maskBuild build)) b) ≤ chainError (t+2*LENGTH+t) := by
    have d := measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression)
      (fun c => chainNonceGame c (fun r => chainPublicComp a t build c b (fun i => maskSalt (r i))))
      (fun c => iidNonceGame c (fun r => chainPublicComp a t build c b (fun i => maskSalt (r i))))
      (δ := chainError (t+2*LENGTH+t)) (by unfold chainError;positivity)
      (fun c => nonce_chain_oracle_distance _ _ _ (fun r => chain_comp_bound a h build c b _))
    simpa only [measureTVDist,chain_grouped a h build b,iid_grouped a h build b] using d
  refine le_min (measureTVDist_le_one _ _) ?_
  by_cases small : t+1 ≤ 2^120
  swap
  · apply (measureTVDist_le_one _ _).trans
    have large : 2^120 ≤ t+1 := by omega
    have castLarge : (2:ℝ)^120 ≤ (t:ℝ)+1 := by exact_mod_cast large
    exact (le_div_iff₀ (by positivity : 0<(2:ℝ)^120)).2 (by simpa using castLarge)
  have old : measureTVDist (sampledReferenceView a (pinnedMaskedView (maskBuild build)) false)
      (sampledReferenceView a (pinnedMaskedView (maskBuild build)) true) ≤ 3*((t:ℝ)+1)/2^122 := by
    unfold measureTVDist
    rw [(pinned_sampled_reference_eq a (maskBuild build) false).evalDist_eq,
      (pinned_sampled_reference_eq a (maskBuild build) true).evalDist_eq]
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
    intro c
    exact shared_final_reference_hiding_sharp a (maskBuild build) c t h small
  have right := side true
  rw [measureTVDist_comm] at right
  have combined := (measureTVDist_triangle (sampledChain a build false) (sampledReferenceView a (pinnedMaskedView (maskBuild build)) false) _).trans
    (add_le_add (side false) ((measureTVDist_triangle _ (sampledReferenceView a (pinnedMaskedView (maskBuild build)) true) _).trans (add_le_add old right)))
  refine combined.trans ?_
  have bound := chain_budget t
  unfold chainError
  linarith

def ChainTranscriptRefines (scheme : Scheme) (build : TranscriptBuilder) : Prop :=
  ∀ (o : Oracle) (m : Message) (p : Positions), fixedOracleRun o (executableTranscript scheme m p) =ᵈ
    (do let k ← $ᵗ Key
        pure (pinnedHonestView build o.compression (BiPermutation.equiv Block o.permutation) m p (maskedNonces o.permutation k)))

private theorem executable_to_chain {State Output : Type} {openingSize : Nat}
    (scheme : Scheme) (build : TranscriptBuilder) (refines : ChainTranscriptRefines scheme build)
    (adversary : Hiding.HidingAdversary State Output openingSize) (which : Bool) :
    Hiding.runHiding (Hiding.hidingExperiment scheme adversary which) =ᵈ
      sampledChain adversary build which := by
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
  unfold sampledChain
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
theorem scheme_hiding_of_chain (scheme : Scheme) (build : TranscriptBuilder)
    (refines : ChainTranscriptRefines scheme build) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  constructor
  · intro _ budget
    positivity
  · intro openingSize budget _ State Output adversary bounded
    unfold measureTVDist
    rw [(executable_to_chain scheme build refines adversary false).evalDist_eq,
      (executable_to_chain scheme build refines adversary true).evalDist_eq]
    exact chain_reference_hiding adversary bounded build

end TwoPermutationPrototype.Sampling
