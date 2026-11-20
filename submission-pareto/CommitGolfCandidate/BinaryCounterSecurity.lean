import CommitGolfCandidate.NonceChainSecurity
import CommitGolfCandidate.CounterSaltOracle

/-! Hiding for the packed binary tree with dadon's keyed counter-mode salts (2a19be00's `CounterSalt` layout).
This is `NonceChainSecurity` with the counter game of `CounterSaltOracle` in place of the chain game: the
honest view is sampled with `CounterSalt.salts π k` for a uniform 192-bit key `k`, and the distance to the
independent-salt reference is `counterError` instead of `chainError`. -/

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
open CommitGolfCandidate.Permutation.NonceChain (Key)
local instance binaryCounterDiscrete {α : Type} : MeasurableSpace α := ⊤

noncomputable def sampledCounter {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (build : TranscriptBuilder) (b : Bool) : ProbComp O := do
  let o ← Oracle.sample
  let ch ← fixedOracleRun o a.choose
  let k ← $ᵗ Key
  observeTranscriptView a (pinnedHonestView build) o.compression ch b (BiPermutation.equiv Block o.permutation)
    (Permutation.CounterSalt.salts o.permutation k)

theorem counter_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : TranscriptBuilder) (b : Bool) :
    𝒟[sampledCounter a build b] =
      𝒟[($ᵗ Compression) >>= fun c => counterNonceGame c (chainPublicComp a t build c b)] := by
  simp only [sampledCounter,Oracle.sample,bind_assoc,pure_bind,counterNonceGame]
  apply _root_.evalDist_bind_congr; intro c
  apply _root_.evalDist_bind_congr; intro π
  simp_rw [chain_comp_run a h build (⟨c,π⟩ : Oracle)]
  exact (distribution_bind_comm ($ᵗ Key) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm

theorem counter_reference_hiding {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : TranscriptBuilder) :
    measureTVDist (sampledCounter a build false) (sampledCounter a build true) ≤ min 1 (((t : ℝ)+1)/2^120) := by
  have side (b : Bool) :
      measureTVDist (sampledCounter a build b) (sampledReferenceView a (pinnedHonestView build) b) ≤
        counterError (t+2*LENGTH+t) := by
    have d := measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression)
      (fun c => counterNonceGame c (chainPublicComp a t build c b))
      (fun c => iidNonceGame c (chainPublicComp a t build c b))
      (δ := counterError (t+2*LENGTH+t)) (by unfold counterError;positivity)
      (fun c => counter_oracle_distance _ _ _ (chain_comp_bound a h build c b))
    simpa only [measureTVDist,counter_grouped a h build b,iid_grouped a h build b] using d
  refine le_min (measureTVDist_le_one _ _) ?_
  by_cases small : t+1 ≤ 2^120
  swap
  · apply (measureTVDist_le_one _ _).trans
    have large : 2^120 ≤ t+1 := by omega
    have castLarge : (2:ℝ)^120 ≤ (t:ℝ)+1 := by exact_mod_cast large
    exact (le_div_iff₀ (by positivity : 0<(2:ℝ)^120)).2 (by simpa using castLarge)
  have old : measureTVDist (sampledReferenceView a (pinnedHonestView build) false)
      (sampledReferenceView a (pinnedHonestView build) true) ≤ ((t:ℝ)+1)/2^121 := by
    unfold measureTVDist
    rw [(pinned_sampled_reference_eq a build false).evalDist_eq,(pinned_sampled_reference_eq a build true).evalDist_eq]
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
    intro c
    exact pinned_final_reference_hiding_sharp a build c t h small
  have right := side true
  rw [measureTVDist_comm] at right
  have combined := (measureTVDist_triangle (sampledCounter a build false) (sampledReferenceView a (pinnedHonestView build) false) _).trans
    (add_le_add (side false) ((measureTVDist_triangle _ (sampledReferenceView a (pinnedHonestView build) true) _).trans (add_le_add old right)))
  refine combined.trans ?_
  have bound := Permutation.CounterSalt.budget t
  unfold counterError
  linarith

def CounterTranscriptRefines (scheme : Scheme) (build : TranscriptBuilder) : Prop :=
  ∀ (o : Oracle) (m : Message) (p : Positions), fixedOracleRun o (executableTranscript scheme m p) =ᵈ
    (do let k ← $ᵗ Key
        pure (pinnedHonestView build o.compression (BiPermutation.equiv Block o.permutation) m p
          (Permutation.CounterSalt.salts o.permutation k)))

private theorem executable_to_counter {State Output : Type} {openingSize : Nat}
    (scheme : Scheme) (build : TranscriptBuilder) (refines : CounterTranscriptRefines scheme build)
    (adversary : Hiding.HidingAdversary State Output openingSize) (which : Bool) :
    Hiding.runHiding (Hiding.hidingExperiment scheme adversary which) =ᵈ
      sampledCounter adversary build which := by
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
  unfold sampledCounter
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

/-- An executable transcript refinement with counter-mode salts gives the exact two-stage hiding clause. -/
theorem scheme_hiding_of_counter (scheme : Scheme) (build : TranscriptBuilder)
    (refines : CounterTranscriptRefines scheme build) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  constructor
  · intro _ budget
    positivity
  · intro openingSize budget _ State Output adversary bounded
    unfold measureTVDist
    rw [(executable_to_counter scheme build refines adversary false).evalDist_eq,
      (executable_to_counter scheme build refines adversary true).evalDist_eq]
    exact counter_reference_hiding adversary bounded build

end TwoPermutationPrototype.Sampling
