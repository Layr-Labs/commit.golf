import CommitGolfCandidate.QuartetCounterSecurity
import CommitGolfCandidate.PairHidingCertificate

/-! Pair-heads analog of `QuartetChainView` / `QuartetCounterSecurity`: the keyed counter-mode salt generator
in front of the pair-leaf honest view, with the independent-salt middle term discharged by `pair_iid_hiding`.
Only the leaf digests change (`pairFullLeafDigests`); the query budget per leaf is still two. -/
namespace TwoPermutationPrototype.Sampling.Quartet
open CommitGolf OracleComp CommitGolfCandidate
open CommitGolfCandidate.Permutation.NonceChain (Key)
local instance pairCounterDiscrete {α : Type} : MeasurableSpace α := ⊤
set_option maxRecDepth 8192
set_option maxHeartbeats 650000
set_option exponentiation.threshold 2048

theorem pair_sampled_reference_eq {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : QuartetBuilder)
    (which : Bool) :
    sampledReferenceView adversary (pairHonestView build) which =ᵈ
      (($ᵗ Compression) >>= fun compress => pairViewReference adversary build compress which) := by
  unfold sampledReferenceView Oracle.sample
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right ($ᵗ Compression)
  intro compress
  let : SampleableType (Completion (PermutationCache.empty Block).entries) :=
    (PermutationCache.empty Block).completionSampler
  let next (permutation : Perm) := do
    let challenge ← fixedOracleRun ⟨compress, permutation⟩ adversary.choose
    let salts ← sampleCompleteSaltTape
    observeTranscriptView adversary (pairHonestView build) compress challenge which
      (BiPermutation.equiv Block permutation) salts
  apply (uniform_transport_bind emptyTransport next).trans
  unfold pairViewReference
  apply EvalDistEq.bind_right
  intro completion
  simp only [next, ← eager_fixed_handler, emptyTransport, Equiv.apply_symm_apply]
  rfl

/-! ### Honest public queries for pair leaves -/

def pairQuerySalted (m : Message) (r : CompleteSaltTape) (i : Index) : OracleComp World (BitVec 256) :=
  if i.val%2=0 then do
    let a ← World.query (.inr (.inr (.inl (RV64.packBuffer (evenFirstInput (messageWords m i))))))
    let b ← World.query (.inr (.inr (.inl (RV64.packBuffer
      (evenSecondInput i (saltWords (r i)) (RV64.replyWords a) (messageWords m i))))))
    return outputDigest b
  else querySaltedDigest m r i

theorem pair_query_salted_bound (m : Message) (r : CompleteSaltTape) (i : Index) :
    PublicQueryBound (pairQuerySalted m r i) 2 := by
  unfold pairQuerySalted
  split
  · exact ⟨(by change 1 ≤ 2;omega),fun a => ⟨(by change 1 ≤ 2-1;omega),fun b => trivial⟩⟩
  · exact query_salted_bound m r i

theorem pair_query_salted_run (o : Oracle) (m : Message) (r : CompleteSaltTape) (i : Index) :
    fixedOracleRun o (pairQuerySalted m r i) =
      pure (pairFullLeafDigests (BiPermutation.equiv Block o.permutation) m r i) := by
  unfold pairQuerySalted pairFullLeafDigests pairLeafDigest
  by_cases h : i.val%2=0
  · simp only [if_pos h]
    rw [fixed_oracle_run_public,fixed_oracle_run_public,fixed_oracle_run_pure]
    rfl
  · simp only [if_neg h]
    rw [query_salted_run]
    rfl

def pairQueryDigests (m : Message) (r : CompleteSaltTape) : OracleComp World DigestTape := do
  let ds ← queryList (pairQuerySalted m r) (List.finRange LENGTH)
  return fun i => ds[i.val]?.getD 0

attribute [local irreducible] List.finRange queryList querySaltedDigest quartetQuery pairQuerySalted

theorem pair_query_digests_bound (m : Message) (r : CompleteSaltTape) :
    PublicQueryBound (pairQueryDigests m r) (2*LENGTH) := by
  have h := public_query_bound_bind (query_list_bound _ 2 (pair_query_salted_bound m r) (List.finRange LENGTH))
    (fun ds => show PublicQueryBound (pure (fun i : Index => ds[i.val]?.getD 0) : OracleComp World _) 0 from trivial)
  simpa only [pairQueryDigests,List.length_finRange,Nat.add_zero,Nat.mul_comm] using h

theorem pair_query_digests_run (o : Oracle) (m : Message) (r : CompleteSaltTape) :
    fixedOracleRun o (pairQueryDigests m r) = pure (pairFullLeafDigests (BiPermutation.equiv Block o.permutation) m r) := by
  rw [pairQueryDigests,fixed_oracle_run_bind,query_list_reference o _ _ _ (fun i _ => pair_query_salted_run o m r i),
    pure_bind,fixed_oracle_run_pure]
  apply congrArg pure
  funext i
  rw [List.getElem?_eq_getElem (by simp [i.isLt])]
  simp

/-- Stage one, the honest pair-leaf and quartet queries on the salt array `r`, then stage two. -/
noncomputable def pairChainPublicComp {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (t : Nat) (c : Compression) (b : Bool) (r : CompleteSaltTape) : OracleComp World O := do
  let ch ← a.choose
  let ds ← pairQueryDigests (if b then ch.message₁ else ch.message₀) r
  let qs ← queryQuartets ds
  let view := builderFrom (fun g => qs.getD g 0) c ch.positions (fun i => r i.val) ds
  guardedView a t ch.aux view.1 view.2

attribute [local irreducible] pairQueryDigests queryQuartets guardedView

theorem pair_chain_comp_bound {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (c : Compression) (b : Bool) (r : CompleteSaltTape) :
    PublicQueryBound (pairChainPublicComp a t c b r) (t + (2*LENGTH + (4194304 + t))) := by
  unfold pairChainPublicComp
  apply public_query_bound_bind (hiding_choose_query_bound a h)
  intro ch
  apply public_query_bound_bind (pair_query_digests_bound _ _)
  intro ds
  apply public_query_bound_bind (query_quartets_bound ds)
  intro qs
  exact guarded_view_bound a t ch.aux _ _

theorem pair_chain_comp_run {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (o : Oracle) (b : Bool) (r : CompleteSaltTape) :
    fixedOracleRun o (pairChainPublicComp a t o.compression b r) =
      (do let ch ← fixedOracleRun o a.choose
          observeTranscriptView a (pairHonestView builder) o.compression ch b (BiPermutation.equiv Block o.permutation) r) := by
  rw [pairChainPublicComp,fixed_oracle_run_bind]
  apply bind_congr_of_forall_mem_support
  intro ch hit
  rw [fixed_oracle_run_bind,pair_query_digests_run,pure_bind,fixed_oracle_run_bind,query_quartets_run,pure_bind,
    reached_view o a h ch hit]
  let p := BiPermutation.equiv Block o.permutation
  let message := if b then ch.message₁ else ch.message₀
  let ds := pairFullLeafDigests p message r
  have same := builder_from_congr
    (fun g => ((List.range 4194304).map (fun g => quartetLookup p (quartetPayload ds g))).getD g 0)
    (fun g => quartetLookup p (quartetPayload ds g)) (fun g inside => queried_quartets p ds g inside)
    o.compression ch.positions (fun i => r i.val) ds
  simp only [observeTranscriptView,pairHonestView,fixedOracle,Equiv.symm_apply_apply,builder_eq_from]
  rw [same]

/-! ### Counter-mode salts against independent salts -/

noncomputable def pairSampledCounter {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n) (b : Bool) : ProbComp O := do
  let o ← Oracle.sample
  let ch ← fixedOracleRun o a.choose
  let k ← $ᵗ Key
  observeTranscriptView a (pairHonestView builder) o.compression ch b (BiPermutation.equiv Block o.permutation)
    (Permutation.CounterSalt.salts o.permutation k)

theorem pair_counter_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (b : Bool) :
    𝒟[pairSampledCounter a b] =
      𝒟[($ᵗ Compression) >>= fun c => counterNonceGame c (pairChainPublicComp a t c b)] := by
  simp only [pairSampledCounter,Oracle.sample,bind_assoc,pure_bind,counterNonceGame]
  apply _root_.evalDist_bind_congr; intro c
  apply _root_.evalDist_bind_congr; intro π
  simp_rw [pair_chain_comp_run a h (⟨c,π⟩ : Oracle)]
  exact (distribution_bind_comm ($ᵗ Key) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm

theorem pair_iid_grouped {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (b : Bool) :
    𝒟[sampledReferenceView a (pairHonestView builder) b] =
      𝒟[($ᵗ Compression) >>= fun c => iidNonceGame c (pairChainPublicComp a t c b)] := by
  simp only [sampledReferenceView,Oracle.sample,bind_assoc,pure_bind,iidNonceGame]
  apply _root_.evalDist_bind_congr; intro c
  trans 𝒟[do let π ← $ᵗ Perm
             let r ← $ᵗ SaltArray
             fixedOracleRun ⟨c,π⟩ (pairChainPublicComp a t c b r)]
  · apply _root_.evalDist_bind_congr; intro π
    simp_rw [pair_chain_comp_run a h (⟨c,π⟩ : Oracle)]
    exact (distribution_bind_comm ($ᵗ SaltArray) (fixedOracleRun ⟨c,π⟩ a.choose) _).symm
  · exact distribution_bind_comm _ _ _

theorem pair_counter_reference_hiding {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) :
    measureTVDist (pairSampledCounter a false) (pairSampledCounter a true) ≤ min 1 (((t : ℝ)+1)/2^120) := by
  have side (b : Bool) :
      measureTVDist (pairSampledCounter a b) (sampledReferenceView a (pairHonestView builder) b) ≤
        counterError (t + (2*LENGTH + (4194304 + t))) := by
    have d := measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression)
      (fun c => counterNonceGame c (pairChainPublicComp a t c b))
      (fun c => iidNonceGame c (pairChainPublicComp a t c b))
      (δ := counterError (t + (2*LENGTH + (4194304 + t)))) (by unfold counterError;positivity)
      (fun c => counter_oracle_distance _ _ _ (pair_chain_comp_bound a h c b))
    simpa only [measureTVDist,pair_counter_grouped a h b,pair_iid_grouped a h b] using d
  refine le_min (measureTVDist_le_one _ _) ?_
  by_cases small : t+1 ≤ 2^120
  swap
  · apply (measureTVDist_le_one _ _).trans
    have large : 2^120 ≤ t+1 := by omega
    have castLarge : (2:ℝ)^120 ≤ (t:ℝ)+1 := by exact_mod_cast large
    exact (le_div_iff₀ (by positivity : 0<(2:ℝ)^120)).2 (by simpa using castLarge)
  have old : measureTVDist (sampledReferenceView a (pairHonestView builder) false)
      (sampledReferenceView a (pairHonestView builder) true) ≤ ((t:ℝ)+1)/2^121 := by
    unfold measureTVDist
    rw [(pair_sampled_reference_eq a builder false).evalDist_eq,(pair_sampled_reference_eq a builder true).evalDist_eq]
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
    intro c
    exact pair_iid_hiding a builder c t h small
  have right := side true
  rw [measureTVDist_comm] at right
  have combined := (measureTVDist_triangle (pairSampledCounter a false) (sampledReferenceView a (pairHonestView builder) false) _).trans
    (add_le_add (side false) ((measureTVDist_triangle _ (sampledReferenceView a (pairHonestView builder) true) _).trans
      (add_le_add old right)))
  refine combined.trans ?_
  have bound := quartet_counter_budget t
  unfold counterError
  linarith

/-- The executable commitment's transcript is the honest pair-leaf Quartet view of counter salts from a uniform key. -/
def PairCounterRefines (scheme : Scheme) : Prop :=
  ∀ (o : Oracle) (m : Message) (p : Positions), fixedOracleRun o (executableTranscript scheme m p) =ᵈ
    (do let k ← $ᵗ Key
        pure (pairHonestView builder o.compression (BiPermutation.equiv Block o.permutation) m p
          (Permutation.CounterSalt.salts o.permutation k)))

private theorem pair_executable_to_counter {State Output : Type} {openingSize : Nat}
    (scheme : Scheme) (refines : PairCounterRefines scheme)
    (adversary : Hiding.HidingAdversary State Output openingSize) (which : Bool) :
    Hiding.runHiding (Hiding.hidingExperiment scheme adversary which) =ᵈ
      pairSampledCounter adversary which := by
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
  unfold pairSampledCounter
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

/-- An executable pair-leaf counter-salt refinement gives the challenge's two-stage hiding clause. -/
theorem scheme_hiding_of_pair_counter (scheme : Scheme) (refines : PairCounterRefines scheme) :
    scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) := by
  constructor
  · intro _ budget
    positivity
  · intro openingSize budget _ State Output adversary bounded
    unfold measureTVDist
    rw [(pair_executable_to_counter scheme refines adversary false).evalDist_eq,
      (pair_executable_to_counter scheme refines adversary true).evalDist_eq]
    exact pair_counter_reference_hiding adversary bounded

end TwoPermutationPrototype.Sampling.Quartet
