import CommitGolfCandidate.MirrorHidingObserver
import CommitGolfCandidate.TwoPermutationHidingTwoStage
import CommitGolfCandidate.HidingQueries

/-! # Hiding for a mirrored leaf: the conditional two-message game

Counterpart of `C3HidingConditional`. After the adversary's first stage and the opened leaves'
rows, the unopened rows are sampled lazily (`conditionalGame`). Replacing them by independent
proposals costs the proposal conflicts, programming them over a uniform digest tape costs the
observer's hits, and the reference world does not depend on the message.

The opened rows are no longer kept apart from the unopened inputs by their tags. The distance of
the conditional game therefore carries `openedHit` for both messages
(`conditional_two_message_distance`), and `two_phase_reference_hiding` averages those two terms
over the opened salts (`distance_bind_le_add_events`), where each is at most `repeatAllowance`
(`opened_hidden_coincide_le`). All distances are extended reals until the last step. -/
namespace TwoPermutationPrototype.Sampling.Mirror
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option exponentiation.threshold 2048
set_option autoImplicit false

noncomputable local instance conditionalFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

local instance conditionalDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

variable (Λ : MirrorLayout)

noncomputable def unpackDigests (positions : Positions) (tape : List Block) : UnopenedDigestTape positions :=
  fun i => ((tape[(hiddenIndices positions).idxOf i]?).map (Λ.digest i.val)).getD 0

theorem unpack_hidden_tape {positions : Positions} (opened : OpenedDigests positions)
    (closed : UnopenedDigestTape positions) (hidden : KeyTape positions) :
    unpackDigests Λ positions
      ((hiddenIndices positions).map (hiddenReply Λ (fullDigestTape opened closed) hidden)) = closed := by
  funext i
  have belongs : i ∈ hiddenIndices positions := by simp [hiddenIndices]
  unfold unpackDigests
  simp only [List.getElem?_map, List.getElem?_idxOf belongs, Option.map_some, Option.getD_some]
  have hit : fullDigestTape opened closed i.val = closed i := by
    unfold fullDigestTape
    exact dite_eq_right i.property
  change Λ.digest i.val (Λ.reply i.val (fullDigestTape opened closed i.val) (hidden i).2) = closed i
  rw [Λ.digest_reply, hit]

noncomputable def conditionalGame {α : Type} {positions : Positions} (cache : Cache) (compress : Compression)
    (messages : Index → Words 32) (opened : OpenedDigests positions)
    (observer : DigestTape → OracleComp World α) (proposed : Bool) : ProbComp α := do
  let salts ← $ᵗ UnopenedSalts positions
  let p ← cache.sample
  let next := fun reverse p => fixedOracleRun (fixedOracle compress p)
    (observer (fullDigestTape opened (unpackDigests Λ positions reverse.reverse)))
  let plans := unopenedPlans Λ positions compress messages (publicSaltTape salts)
  if proposed then runProposed next p.val [] plans else runPlanned next p.val [] plans

noncomputable def conditionalReference {α : Type} {positions : Positions} (cache : Cache)
    (opened : OpenedDigests positions) (compress : Compression)
    (observer : DigestTape → OracleComp World α) : ProbComp α := do
  let digests ← $ᵗ UnopenedDigestTape positions
  let p ← cache.sample
  let _ ← sampleKeyTape positions
  fixedOracleRun (fixedOracle compress p.val) (observer (fullDigestTape opened digests))

noncomputable def conditionalProgrammed {α : Type} {positions : Positions} (cache : Cache)
    (compress : Compression) (messages : Index → Words 32) (opened : OpenedDigests positions)
    (observer : DigestTape → OracleComp World α) : ProbComp α := do
  let digests ← $ᵗ UnopenedDigestTape positions
  let p ← cache.sample
  let hidden ← sampleKeyTape positions
  let all := fullDigestTape opened digests
  fixedOracleRun (fixedOracle compress (p.val.programRows (hiddenRows Λ compress all messages hidden))) (observer all)

theorem conditional_programmed_eq {α : Type} {positions : Positions} (cache : Cache) (compress : Compression)
    (messages : Index → Words 32) (opened : OpenedDigests positions)
    (observer : DigestTape → OracleComp World α) :
    conditionalGame Λ cache compress messages opened observer true =ᵈ
      conditionalProgrammed Λ cache compress messages opened observer := by
  let indices := hiddenIndices positions
  let run (salts : Index → BitVec 128) (tape : List Block) (p : Completion cache.entries) : ProbComp α :=
    fixedOracleRun (fixedOracle compress (p.val.programRows
      (plannedRows [] (unopenedPlans Λ positions compress messages salts) tape)))
      (observer (fullDigestTape opened (unpackDigests Λ positions tape)))
  let finish (salts : Index → BitVec 128) (tape : List Block) : ProbComp α :=
    cache.sample >>= run salts tape
  trans (do let salts ← $ᵗ UnopenedSalts positions
            let tape ← sampleProposalTape indices.length
            finish (publicSaltTape salts) tape)
  · unfold conditionalGame
    apply EvalDistEq.bind_right
    intro salts
    simp only [ite_true]
    let plans := unopenedPlans Λ positions compress messages (publicSaltTape salts)
    have length : plans.length = indices.length := by
      simp [plans, unopenedPlans, indices, leaf_plans_length]
    dsimp only [plans] at length
    simp only [proposed_from_full_tape, length, List.append_nil, List.reverse_reverse]
    exact (EvalDistEq.of_evalDist_eq
      (distribution_bind_comm (sampleProposalTape indices.length) cache.sample (run (publicSaltTape salts)))).symm
  · apply (independent_honest_proposals Λ positions opened finish).trans
    unfold conditionalProgrammed
    apply EvalDistEq.bind_right
    intro digests
    let observeProgrammed (secret : KeyTape positions) (p : Completion cache.entries) : ProbComp α :=
      fixedOracleRun (fixedOracle compress (p.val.programRows
        (hiddenRows Λ compress (fullDigestTape opened digests) messages secret)))
        (observer (fullDigestTape opened digests))
    trans (do let secret ← sampleKeyTape positions
              let p ← cache.sample
              observeProgrammed secret p)
    · apply EvalDistEq.bind_right
      intro secret
      have rows := hidden_rows_match_plans Λ compress (fullDigestTape opened digests) messages secret indices []
      have recovered := unpack_hidden_tape Λ opened digests secret
      simp only [finish, run, observeProgrammed]
      simp only [indices, unopenedPlans, hiddenRows] at rows ⊢
      rw [rows, recovered]
    · exact EvalDistEq.of_evalDist_eq
        (distribution_bind_comm (sampleKeyTape positions) cache.sample observeProgrammed)

/-- The birthday allowance of the honest replies. -/
noncomputable def outputAllowance (budget : Nat) : ENNReal :=
  (2 ^ 24 : ENNReal) * (((budget : ENNReal) + 2 ^ 24) / 2 ^ 1600)

theorem conditional_precharge {α : Type} {positions : Positions} (cache : Cache) (compress : Compression)
    (messages : Index → Words 32) (opened : OpenedDigests positions)
    (observer : DigestTape → OracleComp World α) (firstStage openedRows : List Row) (budget : Nat)
    (seed : cache.entries = openedRows ++ firstStage) (firstCount : firstStage.length ≤ budget)
    (openedCount : openedRows.length ≤ positions.card) :
    measureETVDist (conditionalGame Λ cache compress messages opened observer false)
      (conditionalGame Λ cache compress messages opened observer true) ≤
      (repeatAllowance + ((budget : ENNReal) * hiddenRate +
        openedHit Λ positions compress messages openedRows)) + outputAllowance budget := by
  unfold conditionalGame
  refine (distance_averaged_event ($ᵗ UnopenedSalts positions) _ _
    (fun salts => proposedConflict cache [] (unopenedPlans Λ positions compress messages (publicSaltTape salts)))
    (· = true) ?_).trans
    (honest_proposal_conflict_le Λ cache compress messages firstStage openedRows budget seed
      firstCount openedCount)
  intro salts
  simp only [Bool.false_eq_true, ite_false, ite_true]
  apply planned_vs_proposed_distance

theorem hidden_rate_ne_top : hiddenRate ≠ ⊤ := by
  unfold hiddenRate
  finiteness

theorem conditional_observer_bound {α : Type} {positions : Positions} (cache : Cache) (compress : Compression)
    (messages : Index → Words 32) (opened : OpenedDigests positions)
    (observer : DigestTape → OracleComp World α) (budget : Nat)
    (bounded : ∀ tape, QueryBounded (observer tape) budget) :
    measureETVDist (conditionalReference cache opened compress observer)
      (conditionalProgrammed Λ cache compress messages opened observer) ≤
      (budget : ENNReal) * hiddenRate := by
  have finite : (budget : ENNReal) * hiddenRate ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top budget) hidden_rate_ne_top
  have real : measureTVDist (conditionalReference cache opened compress observer)
      (conditionalProgrammed Λ cache compress messages opened observer) ≤
      ((budget : ENNReal) * hiddenRate).toReal := by
    unfold conditionalReference conditionalProgrammed
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ ENNReal.toReal_nonneg
    intro digests
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ ENNReal.toReal_nonneg
    intro p
    exact independent_hidden_observer_distance Λ positions (fullDigestTape opened digests) messages
      compress p.val (observer (fullDigestTape opened digests)) budget (bounded _)
  rw [measureTVDist_eq_toReal_measureETVDist] at real
  exact (ENNReal.toReal_le_toReal (measureETVDist_ne_top _ _) finite).mp real

/-- What two messages cost apart from the opened rows. -/
noncomputable def messageAllowance (budget : Nat) : ENNReal :=
  repeatAllowance + ((budget : ENNReal) * hiddenRate + (budget : ENNReal) * hiddenRate) +
    outputAllowance budget

/-- **Two messages in the conditional game.** The opened rows enter through `openedHit` only. -/
theorem conditional_two_message_distance {α : Type} {positions : Positions} (cache : Cache)
    (compress : Compression) (messages₀ messages₁ : Index → Words 32) (opened : OpenedDigests positions)
    (observer : DigestTape → OracleComp World α) (firstStage openedRows : List Row) (budget : Nat)
    (seed : cache.entries = openedRows ++ firstStage) (firstCount : firstStage.length ≤ budget)
    (openedCount : openedRows.length ≤ positions.card)
    (bounded : ∀ tape, QueryBounded (observer tape) budget) :
    measureETVDist (conditionalGame Λ cache compress messages₀ opened observer false)
      (conditionalGame Λ cache compress messages₁ opened observer false) ≤
      (messageAllowance budget + messageAllowance budget) +
        (openedHit Λ positions compress messages₀ openedRows +
          openedHit Λ positions compress messages₁ openedRows) := by
  have leg (messages : Index → Words 32) :
      measureETVDist (conditionalGame Λ cache compress messages opened observer false)
        (conditionalReference cache opened compress observer) ≤
        messageAllowance budget + openedHit Λ positions compress messages openedRows := by
    have first : measureETVDist (conditionalGame Λ cache compress messages opened observer false)
        (conditionalProgrammed Λ cache compress messages opened observer) ≤
        (repeatAllowance + ((budget : ENNReal) * hiddenRate +
          openedHit Λ positions compress messages openedRows)) + outputAllowance budget := by
      unfold measureETVDist
      rw [← (conditional_programmed_eq Λ cache compress messages opened observer).evalDist_eq]
      exact conditional_precharge Λ cache compress messages opened observer firstStage openedRows budget
        seed firstCount openedCount
    have second := conditional_observer_bound Λ cache compress messages opened observer budget bounded
    rw [measureETVDist_comm] at second
    refine (measureETVDist_triangle _ (conditionalProgrammed Λ cache compress messages opened observer) _).trans
      ((add_le_add first second).trans_eq ?_)
    unfold messageAllowance
    ring
  have right := leg messages₁
  rw [measureETVDist_comm] at right
  refine (measureETVDist_triangle _ (conditionalReference cache opened compress observer) _).trans
    ((add_le_add (leg messages₀) right).trans_eq ?_)
  ring

/-! ### Opened rows -/

/-- The input of some opened leaf, for the entries and salts the opened leaves have. -/
def OpenedInput (positions : Positions) (compress : Compression) (messages : Index → Words 32)
    (salts : OpenedSalts positions) (input : Block) : Prop :=
  ∃ i : {i : Index // i ∈ positions}, input = Λ.input compress i.val (messages i.val) (salts i)

theorem prepared_opened_rows (positions : Positions) (compress : Compression) (messages : Index → Words 32)
    (salts : OpenedSalts positions) (cache : Cache) (result : List Block × Cache)
    (possible : result ∈ support (runPrepared cache []
      (leafPlans Λ compress messages (publicOpenedSalts salts) positions.toList))) :
    ∃ rows : List Row, result.2.entries = rows ++ cache.entries ∧ rows.length ≤ positions.card ∧
      ∀ row ∈ rows, OpenedInput Λ positions compress messages salts row.1 := by
  obtain ⟨rows, layout, count, tags⟩ := prepared_support_header cache [] _
    (OpenedInput Λ positions compress messages salts) (by
      intro plan present replies
      unfold leafPlans at present
      obtain ⟨index, included, rfl⟩ := List.mem_map.mp present
      have selected : index ∈ positions := Finset.mem_toList.mp included
      refine ⟨⟨index, selected⟩, ?_⟩
      have salt : publicOpenedSalts salts index = salts ⟨index, selected⟩ := by
        unfold publicOpenedSalts
        exact dif_pos selected
      simp only [salt]) result possible
  refine ⟨rows, layout, count.trans_eq ?_, tags⟩
  rw [leaf_plans_length, Finset.length_toList]

/-- An opened leaf and an unopened leaf with one input, as an event of both salt tapes. -/
def Coincide (positions : Positions) (compress : Compression) (opened messages : Index → Words 32)
    (salts : OpenedSalts positions × UnopenedSalts positions) : Prop :=
  ∃ (i : {i : Index // i ∈ positions}) (j : HiddenIndex positions),
    Λ.input compress i.val (opened i.val) (salts.1 i) =
      Λ.input compress j.val (messages j.val) (salts.2 j)

/-- The opened rows hit an unopened input only on `Coincide`. -/
theorem opened_hit_le_coincide (positions : Positions) (compress : Compression)
    (opened messages : Index → Words 32) (shown : OpenedSalts positions) (rows : List Row)
    (tags : ∀ row ∈ rows, OpenedInput Λ positions compress opened shown row.1) :
    openedHit Λ positions compress messages rows ≤
      Pr{let pair ← (do let closed ← $ᵗ UnopenedSalts positions
                        pure (shown, closed))}[Coincide Λ positions compress opened messages pair] := by
  rw [bind_pure_comp, prEvent_map]
  unfold openedHit
  refine prEvent_mono _ _ _ ?_
  rintro closed ⟨j, row, present, equal⟩
  obtain ⟨i, known⟩ := tags row present
  exact ⟨i, j, known.symm.trans equal⟩

/-! ### Averaging over a common prefix -/

theorem distance_bind_support_le {ι α : Type} (common : ProbComp ι)
    (left right : ι → ProbComp α) (error : ENNReal)
    (each : ∀ value ∈ support common, measureETVDist (left value) (right value) ≤ error) :
    measureETVDist (common >>= left) (common >>= right) ≤ error := by
  refine (measureETVDist_bind_left_le_tsum common left right).trans ?_
  calc
    _ ≤ ∑' x, Pr{let y ← common}[y = x] * error := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases present : x ∈ support common
      · exact mul_le_mul_of_nonneg_left (each x present) zero_le
      · have zero : Pr{let y ← common}[y = x] = 0 :=
          (prEvent_eq_zero_iff common (· = x)).2 (fun y mem equal => present (equal ▸ mem))
        rw [zero, zero_mul, zero_mul]
    _ = _ := by rw [ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul]

/-- A distance that is bounded, for each value of a common prefix, by a constant and two event
probabilities of a continuation of that value, is bounded after the prefix by the constant and
the two probabilities of the joint experiment. -/
theorem distance_bind_le_add_events {ι κ α : Type} (common : ProbComp ι)
    (left right : ι → ProbComp α) (base : ENNReal) (aux : ι → ProbComp κ) (first second : κ → Prop)
    (each : ∀ value ∈ support common, measureETVDist (left value) (right value) ≤
      base + (Pr{let k ← aux value}[first k] + Pr{let k ← aux value}[second k])) :
    measureETVDist (common >>= left) (common >>= right) ≤
      base + (Pr{let k ← common >>= aux}[first k] + Pr{let k ← common >>= aux}[second k]) := by
  refine (measureETVDist_bind_left_le_tsum common left right).trans ?_
  calc
    _ ≤ ∑' x, (Pr{let y ← common}[y = x] * base +
          (Pr{let y ← common}[y = x] * Pr{let k ← aux x}[first k] +
            Pr{let y ← common}[y = x] * Pr{let k ← aux x}[second k])) := by
      apply ENNReal.tsum_le_tsum
      intro x
      by_cases present : x ∈ support common
      · exact (mul_le_mul_of_nonneg_left (each x present) zero_le).trans_eq (by ring)
      · have zero : Pr{let y ← common}[y = x] = 0 :=
          (prEvent_eq_zero_iff common (· = x)).2 (fun y mem equal => present (equal ▸ mem))
        rw [zero]
        simp
    _ = _ := by
      rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_prEvent_eq_one, one_mul,
        prEvent_bind_eq_tsum, prEvent_bind_eq_tsum]

/-! ### The two-phase reference -/

noncomputable def readOpenedDigests (positions : Positions) (tape : List Block) : OpenedDigests positions :=
  fun i => ((tape[positions.toList.idxOf i.val]?).map (Λ.digest i.val)).getD 0

noncomputable def twoPhaseReference {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) : ProbComp Output := do
  let (challenge, initial) ← lazyRun compress adversary.choose (PermutationCache.empty Block)
  let salts ← $ᵗ OpenedSalts challenge.positions
  let plans := leafPlans Λ compress (messageWords challenge.message₀) (publicOpenedSalts salts)
    challenge.positions.toList
  let (raw, seeded) ← runPrepared initial [] plans
  let observer := fun tape =>
    let (root, proof) := build compress challenge.positions salts tape
    adversary.observe challenge.aux root proof
  let message := if which then challenge.message₁ else challenge.message₀
  conditionalGame Λ seeded compress (messageWords message)
    (readOpenedDigests Λ challenge.positions raw.reverse) observer false

theorem two_stage_observe_bound {State Output : Type} {openingSize budget : Nat}
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

/-- Everything two messages cost: two message allowances and two coincidence allowances. -/
noncomputable def mirrorAllowance (budget : Nat) : ENNReal :=
  (messageAllowance budget + messageAllowance budget) + (repeatAllowance + repeatAllowance)

/-- **The two worlds of the two-phase reference**, as an extended distance. -/
theorem two_phase_reference_distance {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (budget : Nat) (bounded : Hiding.QueryBound adversary budget) :
    measureETVDist (twoPhaseReference Λ adversary build compress false)
      (twoPhaseReference Λ adversary build compress true) ≤ mirrorAllowance budget := by
  unfold twoPhaseReference
  apply distance_bind_support_le
  intro first inFirst
  have before : first.2.entries.length ≤ budget := by
    have count := lazy_cache_length compress adversary.choose (PermutationCache.empty Block) budget
      (hiding_choose_query_bound adversary bounded) first inFirst
    simpa only [PermutationCache.empty, List.length_nil, Nat.zero_add] using count
  let positions := first.1.positions
  let opened := messageWords first.1.message₀
  let aux (shown : OpenedSalts positions) : ProbComp (OpenedSalts positions × UnopenedSalts positions) := do
    let closed ← $ᵗ UnopenedSalts positions
    pure (shown, closed)
  have averaged := distance_bind_le_add_events ($ᵗ OpenedSalts positions)
    (fun salts => (runPrepared first.2 []
        (leafPlans Λ compress opened (publicOpenedSalts salts) positions.toList)) >>= fun prepared =>
      conditionalGame Λ prepared.2 compress (messageWords first.1.message₀)
        (readOpenedDigests Λ positions prepared.1.reverse)
        (fun tape => adversary.observe first.1.aux (build compress positions salts tape).1
          (build compress positions salts tape).2) false)
    (fun salts => (runPrepared first.2 []
        (leafPlans Λ compress opened (publicOpenedSalts salts) positions.toList)) >>= fun prepared =>
      conditionalGame Λ prepared.2 compress (messageWords first.1.message₁)
        (readOpenedDigests Λ positions prepared.1.reverse)
        (fun tape => adversary.observe first.1.aux (build compress positions salts tape).1
          (build compress positions salts tape).2) false)
    (messageAllowance budget + messageAllowance budget) aux
    (Coincide Λ positions compress opened (messageWords first.1.message₀))
    (Coincide Λ positions compress opened (messageWords first.1.message₁)) (by
      intro salts _
      apply distance_bind_support_le
      intro prepared inPrepared
      obtain ⟨rows, layout, count, tags⟩ := prepared_opened_rows Λ positions compress opened salts
        first.2 prepared inPrepared
      refine (conditional_two_message_distance Λ prepared.2 compress _ _ _ _ first.2.entries rows budget
        layout before count (fun tape =>
          two_stage_observe_bound adversary bounded compress first inFirst _ _)).trans ?_
      exact add_le_add le_rfl (add_le_add
        (opened_hit_le_coincide Λ positions compress opened _ salts rows tags)
        (opened_hit_le_coincide Λ positions compress opened _ salts rows tags)))
  refine (le_of_eq_of_le ?_ averaged).trans ?_
  · simp only [Bool.false_eq_true, ite_false, ite_true]
    rfl
  · unfold mirrorAllowance
    exact add_le_add le_rfl (add_le_add
      (opened_hidden_coincide_le Λ positions compress opened (messageWords first.1.message₀))
      (opened_hidden_coincide_le Λ positions compress opened (messageWords first.1.message₁)))

end TwoPermutationPrototype.Sampling.Mirror
