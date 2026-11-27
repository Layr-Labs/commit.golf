import CommitGolfCandidate.PtrHidingStage
import CommitGolfCandidate.LateHidingSalts
set_option Elab.async false

/-! Statistical hiding of the abstract chained scheme `Chained.Binary.scheme` with shared-midpoint salts.

The contract's two-stage experiment is rewritten exactly: the first stage runs
under lazy compression sampling and leaves a cache; the per-pair coin draws
become uniform pair words, whose two salts share a midpoint; the one-pass tree
and opening become pure functions of the table extending that cache. What
remains is `observation`, bounded in `PtrHidingStage`. Both adaptive stages keep their coins, their
oracle access and their shared budget, and the opening size is arbitrary.
The statements and proofs are those of `S4HidingGame` with the chained tree of
`S5Model`, whose `towerCost 24 LENGTH` parent calls also stay below `LENGTH`.
The staged-game glue follows the base tree's `HidingGameIntegration` and
`HidingSecurity` (dadon's c9b8af82). -/
namespace CommitGolfCandidate.PtrHiding
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
  let retained ← Chained.Binary.treeM Late.hash message salt
  observe (Late.node retained LOG_LENGTH 0) (Chained.Binary.opening retained salt positions)

theorem hiding_experiment_eq (check : Late.Checker) {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (selectSecond : Bool) :
    Hiding.hidingExperiment (Chained.Binary.scheme check) adversary selectSecond =
      (do let challenge ← adversary.choose
          continuation (if selectSecond then challenge.message₁ else challenge.message₀)
            challenge.positions (adversary.observe challenge.aux)) := by
  simp only [Hiding.hidingExperiment, Chained.Binary.scheme, continuation, bind_assoc, pure_bind]

/-- Under a fixed oracle the honest half is uniform pair words followed by the
pure one-pass view. -/
theorem continuation_run {α : Type} (oracle : Oracle) (message : Message)
    (positions : Positions) (observe : Commitment → Proof → OracleComp World α) :
    𝒟[fixedOracleRun oracle (continuation message positions observe)] =
      𝒟[($ᵗ (PairIndex → Late.PairCoins)) >>= fun words =>
        view oracle message (unpackTape words) positions observe] := by
  unfold continuation
  rw [sample_salts_run]
  apply _root_.evalDist_bind_congr
  intro words
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
    𝒟[Hiding.runHiding (Hiding.hidingExperiment (Chained.Binary.scheme check) adversary selectSecond)] =
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

/-- The loss of the one-step argument for both messages is below the contract's
120-bit target. The main term is `16 t / 2^128`, one sixteenth of the allowance. -/
theorem hiding_loss_le_target (known budget : Nat) (knownBound : known ≤ budget) :
    2 * afterLoss (known + 3 * LENGTH) budget ≤
      ((budget : ℝ) + 1) / 2^HIDING_SECURITY_BITS := by
  have size : ((LENGTH : Nat) : ℝ) = 2^24 := by norm_num [LENGTH, LOG_LENGTH]
  have half : ((LENGTH / 2 : Nat) : ℝ) = 2^23 := by norm_num [LENGTH, LOG_LENGTH]
  have parents : ((towerCost 24 LENGTH : Nat) : ℝ) ≤ 2^25 := by
    exact_mod_cast (by decide +kernel : towerCost 24 LENGTH≤2^25)
  have smaller : (known : ℝ) ≤ budget := Nat.cast_le.mpr knownBound
  have nonnegative : (0 : ℝ) ≤ budget := Nat.cast_nonneg _
  have rows : (((known + 3 * LENGTH) * LENGTH + LENGTH * LENGTH : Nat) : ℝ) =
      ((known : ℝ) + 3 * 2^24) * 2^24 + 2^24 * 2^24 := by
    push_cast
    rw [size]
  have tree : ((towerCost 24 LENGTH * LENGTH : Nat) : ℝ) ≤ 2^25 * 2^24 := by
    push_cast
    rw [size]
    exact mul_le_mul_of_nonneg_right parents (by positivity)
  have midpoints : (((LENGTH / 2) ^ 5 : Nat) : ℝ) = (2^23) ^ 5 := by
    push_cast
    rw [half]
  have calls : ((8 * budget : Nat) : ℝ) = 8 * (budget : ℝ) := by push_cast; ring
  unfold afterLoss
  rw [rows, midpoints, calls, show HIDING_SECURITY_BITS = 120 from rfl]
  have bound : 2 * (3 * ((((known : ℝ) + 3 * 2^24) * 2^24 + 2^24 * 2^24) / 2^192) +
      (2^25 * 2^24 : ℝ) / 2^192 + ((2:ℝ)^23) ^ 5 / 2^256 + 8 * (budget : ℝ) / 2^128) ≤
      ((budget : ℝ) + 1) / 2^120 := by
    have common : 2 * (3 * ((((known : ℝ) + 3 * 2^24) * 2^24 + 2^24 * 2^24) / 2^192) +
        (2^25 * 2^24 : ℝ) / 2^192 + ((2:ℝ)^23) ^ 5 / 2^256 + 8 * (budget : ℝ) / 2^128) =
        (2 * (3 * ((((known : ℝ) + 3 * 2^24) * 2^24 + 2^24 * 2^24) * 2^64) +
          (2^25 * 2^24 : ℝ) * 2^64 + ((2:ℝ)^23) ^ 5 + 8 * (budget : ℝ) * 2^128)) / 2^256 := by
      ring
    have target : ((budget : ℝ) + 1) / 2^120 = (((budget : ℝ) + 1) * 2^136) / 2^256 := by ring
    rw [common, target]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [smaller, nonnegative]
  have scaled := div_le_div_of_nonneg_right tree (by positivity : (0 : ℝ) ≤ 2^192)
  linarith

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

/-- Hiding of the abstract chained scheme with shared-midpoint salts at the contract's
error function, for every checker (the hiding experiment never runs it). -/
theorem scheme_hiding (check : Late.Checker) : (Chained.Binary.scheme check).Hiding HIDING_ERROR := by
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

end CommitGolfCandidate.PtrHiding

