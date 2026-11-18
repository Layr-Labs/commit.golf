import CommitGolfCandidate.Probability
import CommitGolfCandidate.S5HideLayer
import CommitGolfCandidate.S4GenHide
import CommitGolfCandidate.HidingQueries

/-! Connect the contract-level reference game to the leaf-layer bound. The second
stage is only bounded after reachable first-stage results, so it is guarded:
after an unreachable state it returns a fixed output without queries. Guarding
does not change the game, and gives the uniform bound the layer argument needs. The
game the machine plays generates its nonces from a seed; one generator step on each
side moves it to the game with uniform nonces. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingGameIntegrationDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleComp.DeferredSampling

variable {State Output : Type} {openingSize : Nat}

/-- The reference game with the nonces generated from a uniform seed (`s4GenNonce`). -/
def hidingGameGen (adversary : Hiding.HidingAdversary State Output openingSize)
    (message : Hiding.HidingChallenge State openingSize → Message) : ProbComp Output := do
  let compression ← $ᵗ Compression
  let permutation ← $ᵗ Perm
  let challenge ← fixedOracleRun ⟨compression, permutation⟩ adversary.choose
  let seed ← $ᵗ BitVec 256
  observeTranscript ⟨compression, permutation⟩ (message challenge)
    (expandTaggedVector (s4GenNonce permutation seed)) challenge.positions (adversary.observe challenge.aux)

/-- Generated nonces versus uniform nonces in the complete reference game: the generator
lemma with the first stage as `first` and the queried transcript plus the second stage as
`next`. -/
theorem hiding_game_gen_distance (adversary : Hiding.HidingAdversary State Output openingSize)
    (budget : Nat) (chooseBound : PublicQueryBound adversary.choose budget)
    (observeBound : ∀ aux root proof, PublicQueryBound (adversary.observe aux root proof) budget)
    (message : Hiding.HidingChallenge State openingSize → Message) :
    measureTVDist (hidingGameGen adversary message) (hidingGame adversary message) ≤
      S5_GEN_LOSS budget ((2 ^ 25 + 2 ^ 23) + budget) := by
  unfold hidingGameGen hidingGame
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by unfold S5_GEN_LOSS; positivity)
  intro compression
  have step := s4_generator_indistinguishable compression adversary.choose
    (fun challenge nonce => observeFull (message challenge) (expandTaggedVector nonce)
      challenge.positions (adversary.observe challenge.aux))
    budget ((2 ^ 25 + 2 ^ 23) + budget) chooseBound
    (fun challenge nonce => observe_full_bound _ _ _ _ budget (observeBound challenge.aux))
  simpa only [observe_full_reference, s4GenSalt] using step

/-- The sampled-oracle reference game is the uniform-nonce game. -/
theorem reference_hiding_game (adversary : Hiding.HidingAdversary State Output openingSize)
    (selectSecond : Bool) :
    (Oracle.sample >>= fun oracle => referenceHiding oracle adversary selectSecond) =
      hidingGame adversary fun challenge =>
        if selectSecond then challenge.message₁ else challenge.message₀ := by
  unfold hidingGame
  simp only [Oracle.sample, bind_assoc, pure_bind]
  rfl

/-- The observing stage, cut off after states for which it has no query bound.
The decision is classical and never evaluated. -/
noncomputable def guardedObserve (adversary : Hiding.HidingAdversary State Output openingSize)
    (budget : Nat) (aux : State) (root : Commitment) (proof : Proof) : OracleComp World Output :=
  @ite _ (∀ root proof, PublicQueryBound (adversary.observe aux root proof) budget)
    (Classical.propDecidable _)
    (adversary.observe aux root proof)
    (pure (OracleComp.support_nonempty (adversary.observe aux root proof)).some)

noncomputable def guardedAdversary (adversary : Hiding.HidingAdversary State Output openingSize)
    (budget : Nat) : Hiding.HidingAdversary State Output openingSize where
  choose := adversary.choose
  observe := guardedObserve adversary budget

theorem guarded_observe_bound (adversary : Hiding.HidingAdversary State Output openingSize)
    (budget : Nat) (aux : State) (root : Commitment) (proof : Proof) :
    PublicQueryBound ((guardedAdversary adversary budget).observe aux root proof) budget := by
  change PublicQueryBound (guardedObserve adversary budget aux root proof) budget
  unfold guardedObserve
  split
  · rename_i bounded
    exact bounded root proof
  · trivial

/-- Any challenge produced under a fixed oracle is a possible syntactic first-stage
result, so the contract's shared query-budget promise applies to it. -/
theorem reached_observe_query_bound {budget : Nat} (oracle : Oracle)
    (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget)
    (challenge : Hiding.HidingChallenge State openingSize)
    (reached : challenge ∈ support (fixedOracleRun oracle adversary.choose))
    (root : Commitment) (proof : Proof) :
    PublicQueryBound (adversary.observe challenge.aux root proof) budget := by
  have possible := fixed_oracle_run_support oracle adversary.choose reached
  have instrumented : challenge ∈ support (Prod.fst <$> Hiding.counted adversary.choose) := by
    have projection : Prod.fst <$> Hiding.counted adversary.choose = adversary.choose :=
      fst_map_costDist adversary.choose ⟨Oracle.callCost⟩
    rw [projection]
    exact possible
  rw [support_map] at instrumented
  obtain ⟨⟨first, calls⟩, counted, equal⟩ := instrumented
  change first = challenge at equal
  subst first
  exact (hiding_observe_query_bound adversary bounded (challenge, calls) counted root proof).mono
    (Nat.sub_le _ _)

/-- The sampled-oracle reference game with generated nonces is `hidingGameGen`. -/
theorem reference_hiding_gen_game (adversary : Hiding.HidingAdversary State Output openingSize)
    (selectSecond : Bool) :
    (Oracle.sample >>= fun oracle => referenceHidingGen oracle adversary selectSecond) =
      hidingGameGen adversary fun challenge =>
        if selectSecond then challenge.message₁ else challenge.message₀ := by
  unfold hidingGameGen
  simp only [Oracle.sample, bind_assoc, pure_bind]
  rfl

theorem guarded_reference {budget : Nat} (oracle : Oracle)
    (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget) (selectSecond : Bool) :
    referenceHiding oracle (guardedAdversary adversary budget) selectSecond =
      referenceHiding oracle adversary selectSecond := by
  unfold referenceHiding
  refine bind_congr_of_forall_mem_support (fixedOracleRun oracle adversary.choose) ?_
  intro challenge reached
  have guard : ∀ root proof, PublicQueryBound (adversary.observe challenge.aux root proof) budget :=
    reached_observe_query_bound oracle adversary bounded challenge reached
  simp only [guardedAdversary, guardedObserve, if_pos guard]

theorem guarded_reference_gen {budget : Nat} (oracle : Oracle)
    (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget) (selectSecond : Bool) :
    referenceHidingGen oracle (guardedAdversary adversary budget) selectSecond =
      referenceHidingGen oracle adversary selectSecond := by
  unfold referenceHidingGen
  refine bind_congr_of_forall_mem_support (fixedOracleRun oracle adversary.choose) ?_
  intro challenge reached
  have guard : ∀ root proof, PublicQueryBound (adversary.observe challenge.aux root proof) budget :=
    reached_observe_query_bound oracle adversary bounded challenge reached
  simp only [guardedAdversary, guardedObserve, if_pos guard]

/-- The leaf-layer step and two generator steps stay below the 120-bit target. -/
theorem hiding_loss_final_le_target (budget : Nat) :
    8 * (budget : ℝ) / 2 ^ 128 + 1 / 2 ^ 130 + 2 * S5_GEN_LOSS budget ((2 ^ 25 + 2 ^ 23) + budget) ≤
      ((budget : ℝ) + 1) / 2 ^ HIDING_SECURITY_BITS := by
  unfold S5_GEN_LOSS
  rw [show HIDING_SECURITY_BITS = 120 from rfl]
  push_cast
  have nonneg : (0 : ℝ) ≤ budget := Nat.cast_nonneg _
  calc _ = (budget : ℝ) * (8 / 2 ^ 128 + 4 / 2 ^ 168) +
        (1 / 2 ^ 130 + 2 * (41943040 + 2097152) / 2 ^ 168) := by ring
    _ ≤ (budget : ℝ) * (1 / 2 ^ 120) + 1 / 2 ^ 120 :=
        add_le_add (mul_le_mul_of_nonneg_left (by norm_num) nonneg) (by norm_num)
    _ = ((budget : ℝ) + 1) / 2 ^ 120 := by ring

/-- Statistical hiding of the reference game with generated nonces, for the
contract's shared two-stage query budget and every opening size: generated to
uniform nonces, all unopened leaves at once, and back. -/
theorem reference_hiding_distance {budget : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget) :
    measureTVDist
      (Oracle.sample >>= fun oracle => referenceHidingGen oracle adversary false)
      (Oracle.sample >>= fun oracle => referenceHidingGen oracle adversary true) ≤
      ((budget : ℝ)+1) / 2^HIDING_SECURITY_BITS := by
  have same (selectSecond : Bool) :
      (Oracle.sample >>= fun oracle => referenceHidingGen oracle adversary selectSecond) =
        hidingGameGen (guardedAdversary adversary budget) fun challenge =>
          if selectSecond then challenge.message₁ else challenge.message₀ := by
    rw [← reference_hiding_gen_game]
    exact congrArg (fun next => Oracle.sample >>= next)
      (funext fun oracle => (guarded_reference_gen oracle adversary bounded selectSecond).symm)
  have chooseBound : PublicQueryBound (guardedAdversary adversary budget).choose budget :=
    hiding_choose_query_bound adversary bounded
  have observeBound := guarded_observe_bound adversary budget
  have uniform : measureTVDist
      (hidingGame (guardedAdversary adversary budget) fun challenge =>
        if false then challenge.message₁ else challenge.message₀)
      (hidingGame (guardedAdversary adversary budget) fun challenge =>
        if true then challenge.message₁ else challenge.message₀) ≤
      8 * (budget : ℝ) / 2 ^ 128 + 1 / 2 ^ 130 :=
    hiding_game_distance (guardedAdversary adversary budget) budget chooseBound observeBound
  have left := hiding_game_gen_distance (guardedAdversary adversary budget) budget chooseBound
    observeBound fun challenge => if false then challenge.message₁ else challenge.message₀
  have right := hiding_game_gen_distance (guardedAdversary adversary budget) budget chooseBound
    observeBound fun challenge => if true then challenge.message₁ else challenge.message₀
  rw [measureTVDist_comm] at right
  rw [same false, same true]
  refine ((measureTVDist_triangle _ (hidingGame (guardedAdversary adversary budget) fun challenge =>
    if false then challenge.message₁ else challenge.message₀) _).trans
    (add_le_add left ((measureTVDist_triangle _ (hidingGame (guardedAdversary adversary budget)
      fun challenge => if true then challenge.message₁ else challenge.message₀) _).trans
      (add_le_add uniform right)))).trans ?_
  have target := hiding_loss_final_le_target budget
  linarith

end CommitGolfCandidate
