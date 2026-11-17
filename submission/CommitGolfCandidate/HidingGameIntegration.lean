import CommitGolfCandidate.Probability
import CommitGolfCandidate.HidingHybrid
import CommitGolfCandidate.HidingQueries

/-! Connect the contract-level reference game to the hybrid games. The second
stage is only bounded after reachable first-stage results, so it is guarded:
after an unreachable state it returns a fixed output without queries. Guarding
does not change the game, and gives the uniform bound the hybrid needs. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingGameIntegrationDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleComp.DeferredSampling

variable {State Output : Type} {openingSize : Nat}

/-- The sampled-oracle reference game is the hybrid game at one end. -/
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

/-- `LENGTH` steps of the per-leaf loss stay below the 120-bit target. -/
theorem hiding_loss_le_target (budget : Nat) :
    (LENGTH : ℝ) *
      (4 * ((budget + ((3*LENGTH-1) + budget) + 4 : Nat) : ℝ) / 2^192) ≤
      ((budget : ℝ)+1) / 2^HIDING_SECURITY_BITS := by
  norm_num [LENGTH,LOG_LENGTH,HIDING_SECURITY_BITS,Nat.cast_add,Nat.cast_mul]
  nlinarith [Nat.cast_nonneg (α := ℝ) budget]

/-- Statistical hiding of the reference game for the stage-3 tree, for the
contract's shared two-stage query budget and every opening size. -/
theorem reference_hiding_distance {budget : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget) :
    measureTVDist
      (Oracle.sample >>= fun oracle => referenceHiding oracle adversary false)
      (Oracle.sample >>= fun oracle => referenceHiding oracle adversary true) ≤
      ((budget : ℝ)+1) / 2^HIDING_SECURITY_BITS := by
  have same (selectSecond : Bool) :
      (Oracle.sample >>= fun oracle => referenceHiding oracle adversary selectSecond) =
        hidingGame (guardedAdversary adversary budget) fun challenge =>
          if selectSecond then challenge.message₁ else challenge.message₀ := by
    rw [← reference_hiding_game]
    exact congrArg (fun next => Oracle.sample >>= next)
      (funext fun oracle => (guarded_reference oracle adversary bounded selectSecond).symm)
  have distance : measureTVDist
      (hidingGame (guardedAdversary adversary budget) fun challenge =>
        if false then challenge.message₁ else challenge.message₀)
      (hidingGame (guardedAdversary adversary budget) fun challenge =>
        if true then challenge.message₁ else challenge.message₀) ≤
      (LENGTH : ℝ) * (4 * ((budget + ((3*LENGTH-1) + budget) + 4 : Nat) : ℝ) / 2^192) :=
    hiding_game_distance (guardedAdversary adversary budget) budget
      (hiding_choose_query_bound adversary bounded) (guarded_observe_bound adversary budget)
  rw [same false, same true]
  exact distance.trans (hiding_loss_le_target budget)

end CommitGolfCandidate
