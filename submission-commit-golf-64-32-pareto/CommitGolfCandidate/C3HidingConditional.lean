import CommitGolfCandidate.C3HidingObserver
import CommitGolfCandidate.TwoPermutationHidingOpened
import CommitGolfCandidate.HidingQueries

/-! # Hiding for the 3c1p leaf: the conditional two-message game

One-row counterparts of the leader's `TwoPermutationHidingConditional`, `Margin`, `Opened` and
`TwoStage`. After the adversary's first stage and the opened leaves' rows, the unopened rows are
sampled lazily (`c3ConditionalGame`). Replacing them by independent proposals costs the
proposal conflicts, programming them over a uniform digest tape costs the observer's hits, and
the reference world with uniform unopened digests does not depend on the message. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option exponentiation.threshold 2048
set_option autoImplicit false

noncomputable local instance c3ConditionalFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

local instance c3ConditionalDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

noncomputable def c3UnpackDigests (positions : Positions) (tape : List Block) : UnopenedDigestTape positions :=
  fun i => (tape.map outputDigest)[(hiddenIndices positions).idxOf i]?.getD 0

theorem c3_unpack_hidden_tape {positions : Positions} (opened : OpenedDigests positions)
    (closed : UnopenedDigestTape positions) (hidden : C3HiddenTape positions) :
    c3UnpackDigests positions
      ((hiddenIndices positions).map (c3HiddenReply (fullDigestTape opened closed) hidden)) = closed := by
  funext i
  have belongs : i ∈ hiddenIndices positions := by simp [hiddenIndices]
  unfold c3UnpackDigests
  rw [List.map_map]
  simp only [List.getElem?_map, List.getElem?_idxOf belongs, Option.map_some, Option.getD_some, Function.comp_apply]
  have hit : fullDigestTape opened closed i.val = closed i := by
    unfold fullDigestTape
    exact dite_eq_right i.property
  change outputDigest ((hidden i).2 ++ fullDigestTape opened closed i.val) = closed i
  rw [hit]
  exact BitVec.extractLsb'_append_eq_right

noncomputable def c3ConditionalGame {α : Type} {positions : Positions} (cache : Cache) (compress : Compression)
    (messages : Index → Words 32) (opened : OpenedDigests positions)
    (observer : DigestTape → OracleComp World α) (proposed : Bool) : ProbComp α := do
  let salts ← $ᵗ UnopenedSalts positions
  let p ← cache.sample
  let next := fun reverse p => fixedOracleRun (fixedOracle compress p)
    (observer (fullDigestTape opened (c3UnpackDigests positions reverse.reverse)))
  let plans := c3UnopenedPlans positions compress messages (publicSaltTape salts)
  if proposed then runProposed next p.val [] plans else runPlanned next p.val [] plans

noncomputable def c3ConditionalReference {α : Type} {positions : Positions} (cache : Cache)
    (opened : OpenedDigests positions) (compress : Compression)
    (observer : DigestTape → OracleComp World α) : ProbComp α := do
  let digests ← $ᵗ UnopenedDigestTape positions
  let p ← cache.sample
  let _ ← sampleC3HiddenTape positions
  fixedOracleRun (fixedOracle compress p.val) (observer (fullDigestTape opened digests))

noncomputable def c3ConditionalProgrammed {α : Type} {positions : Positions} (cache : Cache)
    (compress : Compression) (messages : Index → Words 32) (opened : OpenedDigests positions)
    (observer : DigestTape → OracleComp World α) : ProbComp α := do
  let digests ← $ᵗ UnopenedDigestTape positions
  let p ← cache.sample
  let hidden ← sampleC3HiddenTape positions
  let all := fullDigestTape opened digests
  fixedOracleRun (fixedOracle compress (p.val.programRows (c3HiddenRows compress all messages hidden))) (observer all)

theorem c3_conditional_programmed_eq {α : Type} {positions : Positions} (cache : Cache) (compress : Compression)
    (messages : Index → Words 32) (opened : OpenedDigests positions)
    (observer : DigestTape → OracleComp World α) :
    c3ConditionalGame cache compress messages opened observer true =ᵈ
      c3ConditionalProgrammed cache compress messages opened observer := by
  let indices := hiddenIndices positions
  let run (salts : Index → BitVec 128) (tape : List Block) (p : Completion cache.entries) : ProbComp α :=
    fixedOracleRun (fixedOracle compress (p.val.programRows
      (plannedRows [] (c3UnopenedPlans positions compress messages salts) tape)))
      (observer (fullDigestTape opened (c3UnpackDigests positions tape)))
  let finish (salts : Index → BitVec 128) (tape : List Block) : ProbComp α :=
    cache.sample >>= run salts tape
  trans (do let salts ← $ᵗ UnopenedSalts positions
            let tape ← sampleProposalTape indices.length
            finish (publicSaltTape salts) tape)
  · unfold c3ConditionalGame
    apply EvalDistEq.bind_right
    intro salts
    simp only [ite_true]
    let plans := c3UnopenedPlans positions compress messages (publicSaltTape salts)
    have length : plans.length = indices.length := by
      simp [plans, c3UnopenedPlans, indices, c3_leaf_plans_length]
    dsimp only [plans] at length
    simp only [proposed_from_full_tape, length, List.append_nil, List.reverse_reverse]
    exact (EvalDistEq.of_evalDist_eq
      (distribution_bind_comm (sampleProposalTape indices.length) cache.sample (run (publicSaltTape salts)))).symm
  · apply (c3_independent_honest_proposals positions opened finish).trans
    unfold c3ConditionalProgrammed
    apply EvalDistEq.bind_right
    intro digests
    let observeProgrammed (secret : C3HiddenTape positions) (p : Completion cache.entries) : ProbComp α :=
      fixedOracleRun (fixedOracle compress (p.val.programRows
        (c3HiddenRows compress (fullDigestTape opened digests) messages secret)))
        (observer (fullDigestTape opened digests))
    trans (do let secret ← sampleC3HiddenTape positions
              let p ← cache.sample
              observeProgrammed secret p)
    · apply EvalDistEq.bind_right
      intro secret
      have rows := c3_hidden_rows_match_plans compress (fullDigestTape opened digests) messages secret indices []
      have recovered := c3_unpack_hidden_tape opened digests secret
      simp only [finish, run, observeProgrammed]
      simp only [indices, c3UnopenedPlans, c3HiddenRows] at rows ⊢
      rw [rows, recovered]
    · exact EvalDistEq.of_evalDist_eq
        (distribution_bind_comm (sampleC3HiddenTape positions) cache.sample observeProgrammed)

theorem c3_conditional_precharge {α : Type} {positions : Positions} (cache : Cache) (compress : Compression)
    (messages : Index → Words 32) (opened : OpenedDigests positions)
    (observer : DigestTape → OracleComp World α) (firstStage openedRows : List Row) (budget : Nat)
    (seed : cache.entries = openedRows ++ firstStage) (firstCount : firstStage.length ≤ budget)
    (openedCount : openedRows.length ≤ positions.card)
    (tags : ∀ row ∈ openedRows, c3ExposedTag positions row.1) :
    measureTVDist (c3ConditionalGame cache compress messages opened observer false)
      (c3ConditionalGame cache compress messages opened observer true) ≤
      (budget : ℝ) * c3HiddenRate.toReal + 2 ^ 24 * ((budget : ℝ) + 2 ^ 24) / 2 ^ 1600 := by
  let charge := (budget : ENNReal) * c3HiddenRate + (2 ^ 24 : ENNReal) * (((budget : ENNReal) + 2 ^ 24) / 2 ^ 1600)
  have stepBound : measureETVDist (c3ConditionalGame cache compress messages opened observer false)
      (c3ConditionalGame cache compress messages opened observer true) ≤ charge := by
    unfold c3ConditionalGame
    refine (distance_averaged_event ($ᵗ UnopenedSalts positions) _ _
      (fun salts => proposedConflict cache [] (c3UnopenedPlans positions compress messages (publicSaltTape salts)))
      (· = true) ?_).trans
      (c3_honest_proposal_conflict_le cache compress messages opened firstStage openedRows budget seed
        firstCount openedCount tags)
    intro salts
    simp only [Bool.false_eq_true, ite_false, ite_true]
    apply planned_vs_proposed_distance
  rw [measureTVDist_eq_toReal_measureETVDist]
  refine (ENNReal.toReal_mono (by unfold charge c3HiddenRate; finiteness) stepBound).trans_eq ?_
  unfold charge
  rw [ENNReal.toReal_add (by unfold c3HiddenRate; finiteness) (by finiteness)]
  simp [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_add]
  ring

theorem c3_conditional_observer_bound {α : Type} {positions : Positions} (cache : Cache) (compress : Compression)
    (messages : Index → Words 32) (opened : OpenedDigests positions)
    (observer : DigestTape → OracleComp World α) (budget : Nat)
    (bounded : ∀ tape, QueryBounded (observer tape) budget) :
    measureTVDist (c3ConditionalReference cache opened compress observer)
      (c3ConditionalProgrammed cache compress messages opened observer) ≤
      (budget : ℝ) * c3HiddenRate.toReal := by
  unfold c3ConditionalReference c3ConditionalProgrammed
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
  intro digests
  apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
  intro p
  have each := c3_independent_hidden_observer_distance positions (fullDigestTape opened digests) messages
    compress p.val (observer (fullDigestTape opened digests)) budget (bounded _)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using each

theorem c3_hidden_rate_real_le : c3HiddenRate.toReal ≤ (1 : ℝ) / 2 ^ 127 := by
  unfold c3HiddenRate
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_pow]

theorem c3_two_message_margin (budget : Nat) :
    4 * (budget : ℝ) * c3HiddenRate.toReal +
        4 * 2 ^ 24 * ((budget : ℝ) + 2 ^ 24) / 2 ^ 1600 ≤
      ((budget : ℝ) + 1) / 2 ^ 120 := by
  have nonnegative : 0 ≤ (budget : ℝ) := by positivity
  apply le_trans (add_le_add_left (mul_le_mul_of_nonneg_left c3_hidden_rate_real_le (by positivity)) _)
  norm_num
  linarith

theorem c3_two_message_via_reference {α : Type} (budget : Nat)
    (real₀ programmed₀ reference programmed₁ real₁ : ProbComp α)
    (first₀ : measureTVDist real₀ programmed₀ ≤
      (budget : ℝ) * c3HiddenRate.toReal + 2 ^ 24 * ((budget : ℝ) + 2 ^ 24) / 2 ^ 1600)
    (first₁ : measureTVDist real₁ programmed₁ ≤
      (budget : ℝ) * c3HiddenRate.toReal + 2 ^ 24 * ((budget : ℝ) + 2 ^ 24) / 2 ^ 1600)
    (observe₀ : measureTVDist reference programmed₀ ≤ (budget : ℝ) * c3HiddenRate.toReal)
    (observe₁ : measureTVDist reference programmed₁ ≤ (budget : ℝ) * c3HiddenRate.toReal) :
    measureTVDist real₀ real₁ ≤ min 1 (((budget : ℝ) + 1) / 2 ^ 120) := by
  refine le_min (measureTVDist_le_one _ _) ?_
  have fromFirst := measureTVDist_triangle real₀ programmed₀ reference
  rw [measureTVDist_comm programmed₀ reference] at fromFirst
  have fromSecond := measureTVDist_triangle reference programmed₁ real₁
  rw [measureTVDist_comm programmed₁ real₁] at fromSecond
  have total := measureTVDist_triangle real₀ reference real₁
  calc
    _ ≤ 4 * (budget : ℝ) * c3HiddenRate.toReal +
          4 * 2 ^ 24 * ((budget : ℝ) + 2 ^ 24) / 2 ^ 1600 := by
      norm_num at first₀ first₁ ⊢
      linarith
    _ ≤ _ := c3_two_message_margin budget

theorem c3_conditional_two_message_hiding {α : Type} {positions : Positions} (cache : Cache)
    (compress : Compression) (messages₀ messages₁ : Index → Words 32) (opened : OpenedDigests positions)
    (observer : DigestTape → OracleComp World α) (firstStage openedRows : List Row) (budget : Nat)
    (seed : cache.entries = openedRows ++ firstStage) (firstCount : firstStage.length ≤ budget)
    (openedCount : openedRows.length ≤ positions.card)
    (tags : ∀ row ∈ openedRows, c3ExposedTag positions row.1)
    (bounded : ∀ tape, QueryBounded (observer tape) budget) :
    measureTVDist (c3ConditionalGame cache compress messages₀ opened observer false)
      (c3ConditionalGame cache compress messages₁ opened observer false) ≤
      min 1 (((budget : ℝ) + 1) / 2 ^ 120) := by
  have precharge (message : Index → Words 32) :
      measureTVDist (c3ConditionalGame cache compress message opened observer false)
        (c3ConditionalProgrammed cache compress message opened observer) ≤
        (budget : ℝ) * c3HiddenRate.toReal + 2 ^ 24 * ((budget : ℝ) + 2 ^ 24) / 2 ^ 1600 := by
    unfold measureTVDist
    rw [← (c3_conditional_programmed_eq cache compress message opened observer).evalDist_eq]
    exact c3_conditional_precharge cache compress message opened observer firstStage openedRows budget
      seed firstCount openedCount tags
  exact c3_two_message_via_reference budget _ _ _ _ _ (precharge messages₀) (precharge messages₁)
    (c3_conditional_observer_bound cache compress messages₀ opened observer budget bounded)
    (c3_conditional_observer_bound cache compress messages₁ opened observer budget bounded)

/-! ### Opened rows -/

theorem c3_opened_plan_tag (positions : Positions) (compress : Compression) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (indices : List Index) (allOpened : ∀ i ∈ indices, i ∈ positions)
    (plan : InputPlan) (present : plan ∈ c3LeafPlans compress messages salts indices) (replies : List Block) :
    c3ExposedTag positions (plan replies) := by
  unfold c3LeafPlans at present
  obtain ⟨index, included, rfl⟩ := List.mem_map.mp present
  exact ⟨index, allOpened index included, c3_hidden_tag compress index _ _⟩

theorem c3_prepared_opened_rows (positions : Positions) (compress : Compression) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (cache : Cache) (result : List Block × Cache)
    (possible : result ∈ support (runPrepared cache [] (c3LeafPlans compress messages salts positions.toList))) :
    ∃ rows : List Row, result.2.entries = rows ++ cache.entries ∧ rows.length ≤ positions.card ∧
      ∀ row ∈ rows, c3ExposedTag positions row.1 := by
  obtain ⟨rows, layout, count, tags⟩ := prepared_support_header cache [] _ (c3ExposedTag positions)
    (c3_opened_plan_tag positions compress messages salts positions.toList
      (fun index mem => Finset.mem_toList.mp mem)) result possible
  refine ⟨rows, layout, count.trans_eq ?_, tags⟩
  rw [c3_leaf_plans_length, Finset.length_toList]

/-! ### The two-phase reference -/

noncomputable def c3ReadOpenedDigests (positions : Positions) (tape : List Block) : OpenedDigests positions :=
  fun i => (tape.map outputDigest)[positions.toList.idxOf i.val]?.getD 0

noncomputable def c3TwoPhaseReference {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) : ProbComp Output := do
  let (challenge, initial) ← lazyRun compress adversary.choose (PermutationCache.empty Block)
  let salts ← $ᵗ OpenedSalts challenge.positions
  let plans := c3LeafPlans compress (messageWords challenge.message₀) (publicOpenedSalts salts)
    challenge.positions.toList
  let (raw, seeded) ← runPrepared initial [] plans
  let observer := fun tape =>
    let (root, proof) := build compress challenge.positions salts tape
    adversary.observe challenge.aux root proof
  let message := if which then challenge.message₁ else challenge.message₀
  c3ConditionalGame seeded compress (messageWords message)
    (c3ReadOpenedDigests challenge.positions raw.reverse) observer false

private theorem c3_distance_bind_support_le {ι α : Type} (common : ProbComp ι)
    (left right : ι → ProbComp α) (error : ℝ) (nonneg : 0 ≤ error)
    (each : ∀ value ∈ support common, measureTVDist (left value) (right value) ≤ error) :
    measureTVDist (common >>= left) (common >>= right) ≤ error := by
  apply ENNReal.toReal_le_of_le_ofReal nonneg
  refine (measureETVDist_bind_left_le_tsum common left right).trans ?_
  calc
    _ ≤ ∑' x, Pr{let y ← common}[y = x] * ENNReal.ofReal error := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases present : x ∈ support common
      · exact mul_le_mul_of_nonneg_left
          ((ENNReal.le_ofReal_iff_toReal_le (measureETVDist_ne_top _ _) nonneg).2 (each x present)) zero_le
      · have zero : Pr{let y ← common}[y = x] = 0 :=
          (prEvent_eq_zero_iff common (· = x)).2 (fun y mem equal => present (equal ▸ mem))
        rw [zero, zero_mul, zero_mul]
    _ = _ := by rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

private theorem c3_two_stage_observe_bound {State Output : Type} {openingSize budget : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (bounded : Hiding.QueryBound adversary budget)
    (compress : Compression) (result : Hiding.HidingChallenge State openingSize × Cache)
    (reached : result ∈ support (lazyRun compress adversary.choose (PermutationCache.empty Block)))
    (root : Commitment) (proof : Proof) :
    QueryBounded (adversary.observe result.1.aux root proof) budget := by
  have projected : result.1 ∈ support
      ((simulateQ (lazyHandler compress) adversary.choose).run' (PermutationCache.empty Block)) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨result, reached, rfl⟩
  have possible := support_simulateQ_run'_subset (lazyHandler compress) adversary.choose _ projected
  have instrumented : result.1 ∈ support (Prod.fst <$> Hiding.counted adversary.choose) := by
    rw [show Prod.fst <$> Hiding.counted adversary.choose = adversary.choose from
      fst_map_costDist adversary.choose ⟨Oracle.callCost⟩]
    exact possible
  rw [support_map] at instrumented
  obtain ⟨⟨challenge, calls⟩, counted, equal⟩ := instrumented
  change challenge = result.1 at equal
  subst challenge
  exact (hiding_observe_query_bound adversary bounded (result.1, calls) counted root proof).mono
    (Nat.sub_le _ _)

theorem c3_two_phase_reference_hiding {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (budget : Nat) (bounded : Hiding.QueryBound adversary budget) :
    measureTVDist (c3TwoPhaseReference adversary build compress false)
      (c3TwoPhaseReference adversary build compress true) ≤ min 1 (((budget : ℝ) + 1) / 2 ^ 120) := by
  unfold c3TwoPhaseReference
  apply c3_distance_bind_support_le _ _ _ _ (by positivity)
  intro first inFirst
  apply c3_distance_bind_support_le _ _ _ _ (by positivity)
  intro salts _
  apply c3_distance_bind_support_le _ _ _ _ (by positivity)
  intro opened inOpened
  have before : first.2.entries.length ≤ budget := by
    have count := lazy_cache_length compress adversary.choose (PermutationCache.empty Block) budget
      (hiding_choose_query_bound adversary bounded) first inFirst
    simpa only [PermutationCache.empty, List.length_nil, Nat.zero_add] using count
  obtain ⟨rows, layout, count, tags⟩ := c3_prepared_opened_rows first.1.positions compress
    (messageWords first.1.message₀) (publicOpenedSalts salts) first.2 opened inOpened
  simp only [Bool.false_eq_true, ite_false, ite_true]
  apply c3_conditional_two_message_hiding _ _ _ _ _ _ first.2.entries rows budget layout before count tags
  intro tape
  exact c3_two_stage_observe_bound adversary bounded compress first inFirst _ _

end TwoPermutationPrototype.Sampling
