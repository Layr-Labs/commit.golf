import CommitGolfCandidate.S4HidingHybrid
import CommitGolfCandidate.LateHidingSalts

/-! Statistical hiding of the abstract late-salt scheme `Late.scheme`.

The contract's two-stage experiment is rewritten exactly: the first stage runs
under lazy compression sampling and leaves a cache; the per-pair coin draws
become one uniform salt tape; the one-pass tree and opening become pure
functions of the table extending that cache. What remains is `observation`,
bounded in `LateHidingHybrid`. Both adaptive stages keep their coins, their
oracle access and their shared budget, and the opening size is arbitrary.
The staged-game glue follows the base tree's `HidingGameIntegration` and
`HidingSecurity` (dadon's c9b8af82). -/
namespace CommitGolfCandidate.S4Hiding
open CommitGolfCandidate.LateHiding

-- Observations retain the discrete measurable structure used by the contract.
local instance gameDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

attribute [local irreducible] List.finRange List.range

/-- Honest commitment and opening followed by the observing stage, as one oracle
program. This is the abstract scheme's own code with the trapdoor inlined. -/
def continuation {α : Type} (message : Message) (positions : Positions)
    (observe : Commitment → Proof → OracleComp World α) : OracleComp World α := do
  let salt ← Late.sampleSalts
  let retained ← S4.treeM S4.active Late.hash message salt
  observe (Late.node retained LOG_LENGTH 0) (S4.opening S4.active retained salt positions)

theorem hiding_experiment_eq (check : Late.Checker) {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (selectSecond : Bool) :
    Hiding.hidingExperiment (S4.scheme S4.active check) adversary selectSecond =
      (do let challenge ← adversary.choose
          continuation (if selectSecond then challenge.message₁ else challenge.message₀)
            challenge.positions (adversary.observe challenge.aux)) := by
  simp only [Hiding.hidingExperiment, S4.scheme, continuation, bind_assoc, pure_bind]

/-- Under a fixed oracle the honest half is a uniform salt tape followed by the
pure one-pass view. -/
theorem continuation_run {α : Type} (oracle : Oracle) (message : Message)
    (positions : Positions) (observe : Commitment → Proof → OracleComp World α) :
    𝒟[fixedOracleRun oracle (continuation message positions observe)] =
      𝒟[($ᵗ Late.SaltTape) >>= fun salt => view oracle message salt positions observe] := by
  unfold continuation
  rw [sample_salts_run]
  apply _root_.evalDist_bind_congr
  intro salt
  rw [run_tree]
  rfl

/-- The contract's runner samples the two primitives once and discards the call count. -/
theorem run_hiding_fixed {Output : Type} (experiment : OracleComp World Output) :
    Hiding.runHiding experiment =
      (Oracle.sample >>= fun oracle => fixedOracleRun oracle experiment) := by
  unfold Hiding.runHiding
  apply bind_congr
  intro oracle
  unfold fixedOracleRun
  rw [map_eq_bind_pure_comp]
  apply bind_congr
  intro result
  cases result
  rfl

/-- The hiding game with a lazily sampled first stage. -/
def staged {State Output : Type} {openingSize : Nat} (permutation : Perm)
    (adversary : Hiding.HidingAdversary State Output openingSize) (selectSecond : Bool) :
    ProbComp Output := do
  let result ← compressionRun permutation adversary.choose ∅
  observation permutation result.2
    (if selectSecond then result.1.message₁ else result.1.message₀)
    result.1.positions (adversary.observe result.1.aux)

/-- Exact transition to the cache-conditioned game; no adversary independence is
assumed and neither the cache nor the full oracle is exposed in the output. -/
theorem hiding_staged_distribution (check : Late.Checker) {State Output : Type}
    {openingSize : Nat} (adversary : Hiding.HidingAdversary State Output openingSize)
    (selectSecond : Bool) :
    𝒟[Hiding.runHiding (Hiding.hidingExperiment (S4.scheme S4.active check) adversary selectSecond)] =
      𝒟[($ᵗ Perm) >>= fun permutation => staged permutation adversary selectSecond] := by
  rw [hiding_experiment_eq, run_hiding_fixed]
  simp only [Oracle.sample, bind_assoc, pure_bind]
  trans 𝒟[do let permutation ← $ᵗ Perm
              let table ← $ᵗ Compression
              fixedOracleRun ⟨table, permutation⟩
                (adversary.choose >>= fun challenge =>
                  continuation (if selectSecond then challenge.message₁ else challenge.message₀)
                    challenge.positions (adversary.observe challenge.aux))]
  · exact distribution_bind_comm _ _ _
  · apply _root_.evalDist_bind_congr
    intro permutation
    have lazy := staged_sampling permutation ∅ adversary.choose (fun challenge =>
      continuation (if selectSecond then challenge.message₁ else challenge.message₀)
        challenge.positions (adversary.observe challenge.aux))
    simp only [tableExtending_empty] at lazy
    rw [lazy]
    unfold staged observation
    apply _root_.evalDist_bind_congr
    intro result
    apply _root_.evalDist_bind_congr
    intro table
    exact continuation_run _ _ _ _

/-- Any challenge produced by lazy oracle simulation is a possible syntactic
first-stage result, so the contract's shared query-budget promise applies to it. -/
theorem staged_observe_query_bound {State Output : Type} {openingSize budget : Nat}
    (permutation : Perm) (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget)
    (result : Hiding.HidingChallenge State openingSize × CompressionCache)
    (reached : result ∈ support (compressionRun permutation adversary.choose ∅))
    (root : Commitment) (proof : Proof) :
    PublicQueryBound (adversary.observe result.1.aux root proof) budget := by
  have projected : result.1 ∈ support
      ((simulateQ (compressionHandler permutation) adversary.choose).run' ∅) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨result, reached, rfl⟩
  have possible := support_simulateQ_run'_subset (compressionHandler permutation)
    adversary.choose ∅ projected
  have instrumented : result.1 ∈ support (Prod.fst <$> Hiding.counted adversary.choose) := by
    have projection : Prod.fst <$> Hiding.counted adversary.choose = adversary.choose :=
      fst_map_costDist adversary.choose ⟨Oracle.callCost⟩
    rw [projection]
    exact possible
  rw [support_map] at instrumented
  obtain ⟨⟨challenge, calls⟩, counted, equal⟩ := instrumented
  change challenge = result.1 at equal
  subst challenge
  exact (hiding_observe_query_bound adversary bounded (result.1, calls) counted root proof).mono
    (Nat.sub_le _ _)

/-- The per-leaf loss summed over all `LENGTH` coordinates and both messages is
below the contract's 120-bit target: `2N(2t + 5N + 3) / 2^192 ≤ (t + 1) / 2^120`. -/
theorem hiding_loss_le_target (known budget : Nat) (knownBound : known ≤ budget) :
    (LENGTH : ℝ) * (2 * (((known + 3 + (5 * LENGTH + budget) : Nat) : ℝ) / 2^192)) ≤
      ((budget : ℝ) + 1) / 2^HIDING_SECURITY_BITS := by
  have size : ((LENGTH : Nat) : ℝ) = 2^24 := by norm_num [LENGTH, LOG_LENGTH]
  have total : ((known + 3 + (5 * LENGTH + budget) : Nat) : ℝ) ≤
      (budget : ℝ) + 3 + (5 * 2^24 + budget) := by
    have cast : ((known + 3 + (5 * LENGTH + budget) : Nat) : ℝ) =
        (known : ℝ) + 3 + (5 * (LENGTH : ℝ) + budget) := by push_cast; ring
    have smaller : (known : ℝ) ≤ budget := Nat.cast_le.mpr knownBound
    rw [cast, size]
    linarith
  have nonnegative : (0 : ℝ) ≤ budget := Nat.cast_nonneg _
  have scaled : (LENGTH : ℝ) * (2 * ((budget : ℝ) + 3 + (5 * 2^24 + budget))) ≤
      ((budget : ℝ) + 1) * 2^72 := by
    rw [size]
    nlinarith
  calc (LENGTH : ℝ) * (2 * (((known + 3 + (5 * LENGTH + budget) : Nat) : ℝ) / 2^192))
      ≤ (LENGTH : ℝ) * (2 * (((budget : ℝ) + 3 + (5 * 2^24 + budget)) / 2^192)) := by
        gcongr
    _ = ((LENGTH : ℝ) * (2 * ((budget : ℝ) + 3 + (5 * 2^24 + budget)))) / 2^192 := by ring
    _ ≤ (((budget : ℝ) + 1) * 2^72) / 2^192 := by
        apply div_le_div_of_nonneg_right scaled (by positivity)
    _ = ((budget : ℝ) + 1) / 2^HIDING_SECURITY_BITS := by
        rw [show HIDING_SECURITY_BITS = 120 from rfl]
        rw [div_eq_div_iff (by positivity) (by positivity)]
        ring

/-- Conditional on each reachable first-stage transcript, the fixed-message
hybrid bound applies with at most the original shared public-query budget. -/
theorem staged_distance {State Output : Type} {openingSize budget : Nat}
    (permutation : Perm) (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget) :
    measureTVDist (staged permutation adversary false) (staged permutation adversary true) ≤
      ((budget : ℝ)+1) / 2^HIDING_SECURITY_BITS := by
  unfold staged
  rw [bind_eq_attach_bind (compressionRun permutation adversary.choose ∅)]
  rw [bind_eq_attach_bind (compressionRun permutation adversary.choose ∅)]
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
  rintro ⟨result, reached⟩
  obtain ⟨keys, size, covered⟩ := first_stage_cache_bound permutation adversary.choose budget
    (hiding_choose_query_bound adversary bounded) result reached
  have agree : ∀ index ∈ result.1.positions, result.1.message₀ index = result.1.message₁ index := by
    intro index member
    exact congrFun result.1.agree ⟨index, member⟩
  have distance := observation_distance permutation result.2 keys covered
    result.1.message₀ result.1.message₁ result.1.positions agree
    (adversary.observe result.1.aux) budget
    (staged_observe_query_bound permutation adversary bounded result reached)
  exact distance.trans (hiding_loss_le_target keys.card budget size)

/-- Hiding of the abstract late-salt scheme at the contract's error function, for
every checker (the hiding experiment never runs it). -/
theorem scheme_hiding (check : Late.Checker) : (S4.scheme S4.active check).Hiding HIDING_ERROR := by
  constructor
  · intro openingSize budget
    unfold HIDING_ERROR
    apply le_min (by norm_num)
    positivity
  · intro openingSize budget _ State Output adversary bounded
    apply le_min (measureTVDist_le_one _ _) ?_
    have distance := measureTVDist_bind_left_le_of_forall_le ($ᵗ Perm)
      (fun permutation => staged permutation adversary false)
      (fun permutation => staged permutation adversary true) (by positivity)
      (fun permutation => staged_distance permutation adversary bounded)
    simpa only [measureTVDist, hiding_staged_distribution] using distance

end CommitGolfCandidate.S4Hiding

