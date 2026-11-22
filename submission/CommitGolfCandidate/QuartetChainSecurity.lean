import CommitGolfCandidate.QuartetChainView
import CommitGolfCandidate.QuartetFinalSharp

/-! Adapted from submission c28dd9ca (dadon), `NonceChainSecurity`, for Quartet: the executable
commitment draws a 192-bit key and expands it with the permutation chain; the chain world is within
`CommitGolfCandidate.Permutation.NoncePair.chainError (t + 2·LENGTH + 2^22 + t)` of the independent-salt world on each side, and Quartet's
independent-salt bound at (t+1)/2^121 covers the middle. -/
namespace TwoPermutationPrototype.Sampling.Quartet
open CommitGolf OracleComp CommitGolfCandidate
open CommitGolfCandidate.Permutation.NoncePair (Key actualNonces blocks)
local instance quartetChainSecurityDiscrete {α : Type} : MeasurableSpace α := ⊤

noncomputable def sampledChain {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n) (b : Bool) : ProbComp O := do
  let o ← Oracle.sample
  let ch ← fixedOracleRun o a.choose
  let k ← $ᵗ Key
  observeTranscriptView a (honestView builder) o.compression ch b (BiPermutation.equiv Block o.permutation)
    (actualNonces o.permutation k)

theorem chain_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (b : Bool) :
    𝒟[sampledChain a b] =
      𝒟[($ᵗ Compression) >>= fun c => CommitGolfCandidate.Permutation.NoncePair.chainNonceGame c (chainPublicComp a t c b)] := by
  simp only [sampledChain,Oracle.sample,bind_assoc,pure_bind,CommitGolfCandidate.Permutation.NoncePair.chainNonceGame]
  apply _root_.evalDist_bind_congr; intro c
  apply _root_.evalDist_bind_congr; intro π
  simp_rw [chain_comp_run a h (⟨c,π⟩ : Oracle)]
  exact (distribution_bind_comm ($ᵗ Key) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm

theorem iid_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (b : Bool) :
    𝒟[sampledReferenceView a (honestView builder) b] =
      𝒟[($ᵗ Compression) >>= fun c => CommitGolfCandidate.Permutation.NoncePair.iidNonceGame c (chainPublicComp a t c b)] := by
  simp only [sampledReferenceView,Oracle.sample,bind_assoc,pure_bind,CommitGolfCandidate.Permutation.NoncePair.iidNonceGame]
  apply _root_.evalDist_bind_congr; intro c
  trans 𝒟[do let π ← $ᵗ Perm
             let r ← $ᵗ SaltArray
             fixedOracleRun ⟨c,π⟩ (chainPublicComp a t c b r)]
  · apply _root_.evalDist_bind_congr; intro π
    simp_rw [chain_comp_run a h (⟨c,π⟩ : Oracle)]
    exact (distribution_bind_comm ($ᵗ SaltArray) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm
  · exact distribution_bind_comm _ _ _

/-- The margin: the independent-salt bound plus both chain replacements stays below (t+1)/2^120. -/
theorem quartet_chain_budget (t : Nat) :
    let q := t + (2*LENGTH + (4194304 + t))
    ((t : ℝ)+1)/2^121 + 2 * CommitGolfCandidate.Permutation.NoncePair.chainError q ≤ ((t : ℝ)+1)/2^120 :=
  CommitGolfCandidate.Permutation.NoncePair.quartet_budget t

theorem chain_reference_hiding {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) :
    measureTVDist (sampledChain a false) (sampledChain a true) ≤ min 1 (((t : ℝ)+1)/2^120) := by
  have side (b : Bool) :
      measureTVDist (sampledChain a b) (sampledReferenceView a (honestView builder) b) ≤
        CommitGolfCandidate.Permutation.NoncePair.chainError (t + (2*LENGTH + (4194304 + t))) := by
    have d := measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression)
      (fun c => CommitGolfCandidate.Permutation.NoncePair.chainNonceGame c (chainPublicComp a t c b))
      (fun c => CommitGolfCandidate.Permutation.NoncePair.iidNonceGame c (chainPublicComp a t c b))
      (δ := CommitGolfCandidate.Permutation.NoncePair.chainError (t + (2*LENGTH + (4194304 + t)))) (by unfold CommitGolfCandidate.Permutation.NoncePair.chainError;positivity)
      (fun c => CommitGolfCandidate.Permutation.NoncePair.nonce_chain_oracle_distance _ _ _ (chain_comp_bound a h c b))
    simpa only [measureTVDist,chain_grouped a h b,iid_grouped a h b] using d
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
  have combined := (measureTVDist_triangle (sampledChain a false) (sampledReferenceView a (honestView builder) false) _).trans
    (add_le_add (side false) ((measureTVDist_triangle _ (sampledReferenceView a (honestView builder) true) _).trans
      (add_le_add old right)))
  refine combined.trans ?_
  have bound := quartet_chain_budget t
  unfold CommitGolfCandidate.Permutation.NoncePair.chainError at bound ⊢
  linarith

/-- The executable commitment's transcript is the honest Quartet view of chain salts from a uniform key. -/
def ChainQuartetRefines (scheme : Scheme) : Prop :=
  ∀ (o : Oracle) (m : Message) (p : Positions), fixedOracleRun o (executableTranscript scheme m p) =ᵈ
    (do let k ← $ᵗ Key
        pure (honestView builder o.compression (BiPermutation.equiv Block o.permutation) m p (actualNonces o.permutation k)))

private theorem executable_to_chain {State Output : Type} {openingSize : Nat}
    (scheme : Scheme) (refines : ChainQuartetRefines scheme)
    (adversary : Hiding.HidingAdversary State Output openingSize) (which : Bool) :
    Hiding.runHiding (Hiding.hidingExperiment scheme adversary which) =ᵈ
      sampledChain adversary which := by
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

/-- An executable chain-salt refinement gives the challenge's two-stage hiding clause. -/
theorem scheme_hiding_of_chain (scheme : Scheme) (refines : ChainQuartetRefines scheme) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  constructor
  · intro _ budget
    positivity
  · intro openingSize budget _ State Output adversary bounded
    unfold measureTVDist
    rw [(executable_to_chain scheme refines adversary false).evalDist_eq,
      (executable_to_chain scheme refines adversary true).evalDist_eq]
    exact chain_reference_hiding adversary bounded

end TwoPermutationPrototype.Sampling.Quartet
