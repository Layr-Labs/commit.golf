import CommitGolfCandidate.PentaNonceView
import CommitGolfCandidate.PentaNonceFinal
import CommitGolfCandidate.PentaHidingTransport
import CommitGolfCandidate.CounterSaltOracle

/-! Hiding for the 5-ary tree + 4,095-leaf-period keyed counter-mode salts. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
open CommitGolfCandidate.Permutation.NonceChain (Key)
open CommitGolfCandidate.Permutation.CounterSalt (groups salts)
local instance pentaCounterSecurityDiscrete {α : Type} : MeasurableSpace α := ⊤

theorem penta_counter_budget (t : Nat) :
    let q := t + 2*LENGTH + pentaQueries PENTA_LEVELS + t
    ((t : ℝ)+1)/2^121 +
      2 * ((groups : ℝ) * ((2*q+groups : ℝ)/2^192)) ≤
        ((t : ℝ)+1)/2^120 := by
  simp only [penta_queries_value]
  norm_num [groups,LENGTH,LOG_LENGTH,Nat.cast_add,Nat.cast_mul]
  nlinarith [Nat.cast_nonneg (α := ℝ) t]

noncomputable def sampledPentaCounter {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : PentaTranscriptBuilder) (b : Bool) : ProbComp O := do
  let o ← Oracle.sample
  let ch ← fixedOracleRun o a.choose
  let k ← $ᵗ Key
  observeTranscriptView a (pentaView build) o.compression ch b (BiPermutation.equiv Block o.permutation)
    (salts o.permutation k)

theorem penta_counter_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : PentaTranscriptBuilder) (isLocal : PentaBuildLocal build) (b : Bool) :
    𝒟[sampledPentaCounter a build b] =
      𝒟[($ᵗ Compression) >>= fun c => counterNonceGame c (chainPentaComp a t build b)] := by
  simp only [sampledPentaCounter,Oracle.sample,bind_assoc,pure_bind,counterNonceGame]
  apply _root_.evalDist_bind_congr; intro c
  apply _root_.evalDist_bind_congr; intro π
  simp_rw [chain_penta_comp_run a h build isLocal (⟨c,π⟩ : Oracle)]
  exact (distribution_bind_comm ($ᵗ Key) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm

theorem penta_counter_iid_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : PentaTranscriptBuilder) (isLocal : PentaBuildLocal build) (b : Bool) :
    𝒟[sampledReferenceView a (pentaView build) b] =
      𝒟[($ᵗ Compression) >>= fun c => iidNonceGame c (chainPentaComp a t build b)] := by
  simp only [sampledReferenceView,Oracle.sample,bind_assoc,pure_bind,iidNonceGame]
  apply _root_.evalDist_bind_congr; intro c
  trans 𝒟[do let π ← $ᵗ Perm
             let r ← $ᵗ SaltArray
             fixedOracleRun ⟨c,π⟩ (chainPentaComp a t build b r)]
  · apply _root_.evalDist_bind_congr; intro π
    simp_rw [chain_penta_comp_run a h build isLocal (⟨c,π⟩ : Oracle)]
    exact (distribution_bind_comm ($ᵗ SaltArray) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm
  · exact distribution_bind_comm _ _ _

theorem penta_counter_reference_hiding {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : PentaTranscriptBuilder) (isLocal : PentaBuildLocal build) :
    measureTVDist (sampledPentaCounter a build false) (sampledPentaCounter a build true) ≤
      min 1 (((t : ℝ)+1)/2^120) := by
  have side (b : Bool) :
      measureTVDist (sampledPentaCounter a build b) (sampledReferenceView a (pentaView build) b) ≤
        counterError (t+2*LENGTH+pentaQueries PENTA_LEVELS+t) := by
    have d := measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression)
      (fun c => counterNonceGame c (chainPentaComp a t build b))
      (fun c => iidNonceGame c (chainPentaComp a t build b))
      (δ := counterError (t+2*LENGTH+pentaQueries PENTA_LEVELS+t)) (by unfold counterError;positivity)
      (fun c => counter_oracle_distance _ _ _ (chain_penta_comp_bound a h build b))
    simpa only [measureTVDist,penta_counter_grouped a h build isLocal b,penta_counter_iid_grouped a h build isLocal b] using d
  refine le_min (measureTVDist_le_one _ _) ?_
  by_cases small : t+1 ≤ 2^120
  swap
  · apply (measureTVDist_le_one _ _).trans
    have large : 2^120 ≤ t+1 := by omega
    have castLarge : (2:ℝ)^120 ≤ (t:ℝ)+1 := by exact_mod_cast large
    exact (le_div_iff₀ (by positivity : 0<(2:ℝ)^120)).2 (by simpa using castLarge)
  have old : measureTVDist (sampledReferenceView a (pentaView build) false)
      (sampledReferenceView a (pentaView build) true) ≤ ((t:ℝ)+1)/2^121 := by
    unfold measureTVDist
    rw [(penta_sampled_reference_eq a build false).evalDist_eq,(penta_sampled_reference_eq a build true).evalDist_eq]
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
    intro c
    exact penta_final_reference_hiding_sharp a build c t h small
  have right := side true
  rw [measureTVDist_comm] at right
  have combined := (measureTVDist_triangle (sampledPentaCounter a build false)
    (sampledReferenceView a (pentaView build) false) _).trans
    (add_le_add (side false) ((measureTVDist_triangle _ (sampledReferenceView a (pentaView build) true) _).trans
      (add_le_add old right)))
  refine combined.trans ?_
  have bound := penta_counter_budget t
  unfold counterError
  linarith

def PentaCounterTranscriptRefines (scheme : Scheme) (build : PentaTranscriptBuilder) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions),
    fixedOracleRun oracle (executableTranscript scheme message positions) =ᵈ
      (do let k ← $ᵗ Key
          pure (pentaView build oracle.compression (BiPermutation.equiv Block oracle.permutation)
            message positions (salts oracle.permutation k)))

private theorem executable_to_penta_counter {State Output : Type} {openingSize : Nat}
    (scheme : Scheme) (build : PentaTranscriptBuilder) (refines : PentaCounterTranscriptRefines scheme build)
    (adversary : Hiding.HidingAdversary State Output openingSize) (which : Bool) :
    Hiding.runHiding (Hiding.hidingExperiment scheme adversary which) =ᵈ
      sampledPentaCounter adversary build which := by
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
  unfold sampledPentaCounter
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

theorem penta_counter_hiding_of_transcript (scheme : Scheme) (build : PentaTranscriptBuilder)
    (isLocal : PentaBuildLocal build) (refines : PentaCounterTranscriptRefines scheme build) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  constructor
  · intro _ budget
    positivity
  · intro openingSize budget _ State Output adversary bounded
    unfold measureTVDist
    rw [(executable_to_penta_counter scheme build refines adversary false).evalDist_eq,
      (executable_to_penta_counter scheme build refines adversary true).evalDist_eq]
    exact penta_counter_reference_hiding adversary bounded build isLocal

theorem penta_counter_hiding (scheme : Scheme) (refines : PentaCounterTranscriptRefines scheme pentaTranscriptBuilder) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) :=
  penta_counter_hiding_of_transcript scheme pentaTranscriptBuilder penta_transcript_builder_local refines

end TwoPermutationPrototype.Sampling
