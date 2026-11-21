import CommitGolfCandidate.Quad3NonceView
import CommitGolfCandidate.QuadNonceFinal
import CommitGolfCandidate.QuadHidingTransport
import CommitGolfCandidate.NoncePairOracle

/-! Hiding for quad3 + NonceChain (quad3 analogue of `QuadNonceSecurity`, itself the quad analogue of 31727a8's `NonceChainSecurity`).
Chain salts vs independent salts costs `NoncePair.chainError (2t + 2·LENGTH + LENGTH/4 + LENGTH/16 + LENGTH/64)` per side
(`NoncePair.nonce_chain_oracle_distance`); the independent-salt quad view costs `(t+1)/2^121`
(`quad_final_reference_hiding_sharp`); `quad3_chain_budget` fits the sum under `(t+1)/2^120`. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
open CommitGolfCandidate.Permutation.NoncePair (Key actualNonces blocks)
open CommitGolfCandidate.Permutation
local instance quad3ChainSecurityDiscrete {α : Type} : MeasurableSpace α := ⊤

theorem quad3_chain_budget (t : Nat) :
    let q := t + 2*LENGTH + (LENGTH/4 + (LENGTH/16 + LENGTH/64)) + t
    ((t : ℝ)+1)/2^121 +
      4 * (((blocks+1 : Nat) : ℝ) * ((q+(blocks+1) : ℝ)/2^192)) ≤
        ((t : ℝ)+1)/2^120 := by
  norm_num [blocks,LENGTH,LOG_LENGTH,Nat.cast_add,Nat.cast_mul]
  nlinarith [Nat.cast_nonneg (α := ℝ) t]

noncomputable def sampledQuad3Chain {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : QuadTranscriptBuilder) (b : Bool) : ProbComp O := do
  let o ← Oracle.sample
  let ch ← fixedOracleRun o a.choose
  let k ← $ᵗ Key
  observeTranscriptView a (quadHonestView build) o.compression ch b (BiPermutation.equiv Block o.permutation)
    (actualNonces o.permutation k)

theorem quad3_chain_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : QuadTranscriptBuilder) (isLocal : Quad3BuildLocal build) (b : Bool) :
    𝒟[sampledQuad3Chain a build b] =
      𝒟[($ᵗ Compression) >>= fun c => NoncePair.chainNonceGame c (chainQuad3Comp a t build c b)] := by
  simp only [sampledQuad3Chain,Oracle.sample,bind_assoc,pure_bind,NoncePair.chainNonceGame]
  apply _root_.evalDist_bind_congr; intro c
  apply _root_.evalDist_bind_congr; intro π
  simp_rw [chain_quad3_comp_run a h build isLocal (⟨c,π⟩ : Oracle)]
  exact (distribution_bind_comm ($ᵗ Key) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm

theorem quad3_iid_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : QuadTranscriptBuilder) (isLocal : Quad3BuildLocal build) (b : Bool) :
    𝒟[sampledReferenceView a (quadHonestView build) b] =
      𝒟[($ᵗ Compression) >>= fun c => NoncePair.iidNonceGame c (chainQuad3Comp a t build c b)] := by
  simp only [sampledReferenceView,Oracle.sample,bind_assoc,pure_bind,NoncePair.iidNonceGame]
  apply _root_.evalDist_bind_congr; intro c
  trans 𝒟[do let π ← $ᵗ Perm
             let r ← $ᵗ SaltArray
             fixedOracleRun ⟨c,π⟩ (chainQuad3Comp a t build c b r)]
  · apply _root_.evalDist_bind_congr; intro π
    simp_rw [chain_quad3_comp_run a h build isLocal (⟨c,π⟩ : Oracle)]
    exact (distribution_bind_comm ($ᵗ SaltArray) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm
  · exact distribution_bind_comm _ _ _

theorem quad3_chain_reference_hiding {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : QuadTranscriptBuilder) (isLocal : Quad3BuildLocal build) :
    measureTVDist (sampledQuad3Chain a build false) (sampledQuad3Chain a build true) ≤
      min 1 (((t : ℝ)+1)/2^120) := by
  have side (b : Bool) :
      measureTVDist (sampledQuad3Chain a build b) (sampledReferenceView a (quadHonestView build) b) ≤
        NoncePair.chainError (t+2*LENGTH+(LENGTH/4+(LENGTH/16+LENGTH/64))+t) := by
    have d := measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression)
      (fun c => NoncePair.chainNonceGame c (chainQuad3Comp a t build c b))
      (fun c => NoncePair.iidNonceGame c (chainQuad3Comp a t build c b))
      (δ := NoncePair.chainError (t+2*LENGTH+(LENGTH/4+(LENGTH/16+LENGTH/64))+t)) (by unfold NoncePair.chainError;positivity)
      (fun c => NoncePair.nonce_chain_oracle_distance _ _ _ (chain_quad3_comp_bound a h build c b))
    simpa only [measureTVDist,quad3_chain_grouped a h build isLocal b,quad3_iid_grouped a h build isLocal b] using d
  refine le_min (measureTVDist_le_one _ _) ?_
  by_cases small : t+1 ≤ 2^120
  swap
  · apply (measureTVDist_le_one _ _).trans
    have large : 2^120 ≤ t+1 := by omega
    have castLarge : (2:ℝ)^120 ≤ (t:ℝ)+1 := by exact_mod_cast large
    exact (le_div_iff₀ (by positivity : 0<(2:ℝ)^120)).2 (by simpa using castLarge)
  have old : measureTVDist (sampledReferenceView a (quadHonestView build) false)
      (sampledReferenceView a (quadHonestView build) true) ≤ ((t:ℝ)+1)/2^121 := by
    unfold measureTVDist
    rw [(quad_sampled_reference_eq a build false).evalDist_eq,(quad_sampled_reference_eq a build true).evalDist_eq]
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
    intro c
    exact quad_final_reference_hiding_sharp a build c t h small
  have right := side true
  rw [measureTVDist_comm] at right
  have combined := (measureTVDist_triangle (sampledQuad3Chain a build false)
    (sampledReferenceView a (quadHonestView build) false) _).trans
    (add_le_add (side false) ((measureTVDist_triangle _ (sampledReferenceView a (quadHonestView build) true) _).trans
      (add_le_add old right)))
  refine combined.trans ?_
  have bound := quad3_chain_budget t
  unfold NoncePair.chainError
  linarith

private theorem executable_to_quad3_chain {State Output : Type} {openingSize : Nat}
    (scheme : Scheme) (build : QuadTranscriptBuilder) (refines : QuadNonceTranscriptRefines scheme build)
    (adversary : Hiding.HidingAdversary State Output openingSize) (which : Bool) :
    Hiding.runHiding (Hiding.hidingExperiment scheme adversary which) =ᵈ
      sampledQuad3Chain adversary build which := by
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
  unfold sampledQuad3Chain
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

/-- Hiding of any scheme whose executable transcript is the quad honest view with nonce-chain
salts, for a builder that reads the quad node function only on honest group inputs. -/
theorem quad3_nonce_hiding_of_transcript (scheme : Scheme) (build : QuadTranscriptBuilder)
    (isLocal : Quad3BuildLocal build) (refines : QuadNonceTranscriptRefines scheme build) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  constructor
  · intro _ budget
    positivity
  · intro openingSize budget _ State Output adversary bounded
    unfold measureTVDist
    rw [(executable_to_quad3_chain scheme build refines adversary false).evalDist_eq,
      (executable_to_quad3_chain scheme build refines adversary true).evalDist_eq]
    exact quad3_chain_reference_hiding adversary bounded build isLocal

/-- The form the lead wires into `Solution.lean` (privacy line). -/
theorem quad3_nonce_hiding (scheme : Scheme) (refines : QuadNonceTranscriptRefines scheme quad3TranscriptBuilder) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) :=
  quad3_nonce_hiding_of_transcript scheme quad3TranscriptBuilder quad3_transcript_builder_local refines

end TwoPermutationPrototype.Sampling
