import CommitGolfCandidate.QuartetChainSecurity
import CommitGolfCandidate.CounterSaltOracle
namespace TwoPermutationPrototype.Sampling.Quartet
open CommitGolf OracleComp CommitGolfCandidate
open CommitGolfCandidate.Permutation.NonceChain (Key)
local instance quartetCounterDiscrete {α : Type} : MeasurableSpace α := ⊤

noncomputable def sampledCounter {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n) (b : Bool) : ProbComp O := do
  let o ← Oracle.sample
  let ch ← fixedOracleRun o a.choose
  let k ← $ᵗ Key
  observeTranscriptView a (honestView builder) o.compression ch b (BiPermutation.equiv Block o.permutation)
    (Permutation.CounterSalt.salts o.permutation k)

theorem counter_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (b : Bool) :
    𝒟[sampledCounter a b] =
      𝒟[($ᵗ Compression) >>= fun c => counterNonceGame c (chainPublicComp a t c b)] := by
  simp only [sampledCounter,Oracle.sample,bind_assoc,pure_bind,counterNonceGame]
  apply _root_.evalDist_bind_congr; intro c
  apply _root_.evalDist_bind_congr; intro π
  simp_rw [chain_comp_run a h (⟨c,π⟩ : Oracle)]
  exact (distribution_bind_comm ($ᵗ Key) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm

/-- The margin: the independent-salt bound plus both chain replacements stays below (t+1)/2^120. -/
theorem quartet_counter_budget (t : Nat) :
    let q := t + (2*LENGTH + (4194304 + t))
    ((t : ℝ)+1)/2^121 +
      2 * ((Permutation.CounterSalt.groups : ℝ) * ((2*q+Permutation.CounterSalt.groups : ℝ)/2^192)) ≤
        ((t : ℝ)+1)/2^120 := by
  norm_num [Permutation.CounterSalt.groups,LENGTH,LOG_LENGTH,Nat.cast_add,Nat.cast_mul]
  nlinarith [Nat.cast_nonneg (α := ℝ) t]

theorem counter_reference_hiding {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) :
    measureTVDist (sampledCounter a false) (sampledCounter a true) ≤ min 1 (((t : ℝ)+1)/2^120) := by
  have side (b : Bool) :
      measureTVDist (sampledCounter a b) (sampledReferenceView a (honestView builder) b) ≤
        counterError (t + (2*LENGTH + (4194304 + t))) := by
    have d := measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression)
      (fun c => counterNonceGame c (chainPublicComp a t c b))
      (fun c => iidNonceGame c (chainPublicComp a t c b))
      (δ := counterError (t + (2*LENGTH + (4194304 + t)))) (by unfold counterError;positivity)
      (fun c => counter_oracle_distance _ _ _ (chain_comp_bound a h c b))
    simpa only [measureTVDist,counter_grouped a h b,iid_grouped a h b] using d
  refine le_min (measureTVDist_le_one _ _) ?_
  by_cases small : t+1 ≤ 2^120
  swap
  · apply (measureTVDist_le_one _ _).trans
    have large : 2^120 ≤ t+1 := by omega
    have castLarge : (2:ℝ)^120 ≤ (t:ℝ)+1 := by exact_mod_cast large
    exact (le_div_iff₀ (by positivity : 0<(2:ℝ)^120)).2 (by simpa using castLarge)
  have old : measureTVDist (sampledReferenceView a (honestView builder) false)
      (sampledReferenceView a (honestView builder) true) ≤ ((t:ℝ)+1)/2^121 := by
    unfold measureTVDist
    rw [(sampled_reference_eq a builder false).evalDist_eq,(sampled_reference_eq a builder true).evalDist_eq]
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
    intro c
    exact final_reference_hiding_sharp global_frame a builder c t h small
  have right := side true
  rw [measureTVDist_comm] at right
  have combined := (measureTVDist_triangle (sampledCounter a false) (sampledReferenceView a (honestView builder) false) _).trans
    (add_le_add (side false) ((measureTVDist_triangle _ (sampledReferenceView a (honestView builder) true) _).trans
      (add_le_add old right)))
  refine combined.trans ?_
  have bound := quartet_counter_budget t
  unfold counterError
  linarith

/-- The executable commitment's transcript is the honest Quartet view of chain salts from a uniform key. -/
def CounterQuartetRefines (scheme : Scheme) : Prop :=
  ∀ (o : Oracle) (m : Message) (p : Positions), fixedOracleRun o (executableTranscript scheme m p) =ᵈ
    (do let k ← $ᵗ Key
        pure (honestView builder o.compression (BiPermutation.equiv Block o.permutation) m p (Permutation.CounterSalt.salts o.permutation k)))

private theorem executable_to_counter {State Output : Type} {openingSize : Nat}
    (scheme : Scheme) (refines : CounterQuartetRefines scheme)
    (adversary : Hiding.HidingAdversary State Output openingSize) (which : Bool) :
    Hiding.runHiding (Hiding.hidingExperiment scheme adversary which) =ᵈ
      sampledCounter adversary which := by
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

/-- An executable chain-salt refinement gives the challenge's two-stage hiding clause. -/
theorem scheme_hiding_of_counter (scheme : Scheme) (refines : CounterQuartetRefines scheme) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  constructor
  · intro _ budget
    positivity
  · intro openingSize budget _ State Output adversary bounded
    unfold measureTVDist
    rw [(executable_to_counter scheme refines adversary false).evalDist_eq,
      (executable_to_counter scheme refines adversary true).evalDist_eq]
    exact counter_reference_hiding adversary bounded

end TwoPermutationPrototype.Sampling.Quartet
