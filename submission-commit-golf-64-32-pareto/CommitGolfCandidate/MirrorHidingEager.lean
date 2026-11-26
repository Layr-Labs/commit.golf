import CommitGolfCandidate.MirrorHidingConditional
import CommitGolfCandidate.TwoPermutationHidingBridge

/-! # Hiding for a mirrored leaf: from the contract's game to the conditional game

Counterpart of `C3HidingEager`. The reference experiment samples a full permutation, runs the
adversary's first stage on it, draws the salt tape and shows the honest transcript of
`mirrorView`. Lazily sampling the permutation and moving the opened leaves' calls ahead of the
unopened ones turns it into `twoPhaseReference`, whose two worlds are close by
`two_phase_reference_distance`. The arithmetic is at the end: `mirrorAllowance t` is at most
`t/2^124 + 2^-205`, inside `(t + 1)/2^120`. -/
namespace TwoPermutationPrototype.Sampling.Mirror
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048
set_option autoImplicit false

noncomputable local instance eagerFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

local instance eagerDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

variable (Λ : MirrorLayout)

def leafReply (compress : Compression) (p : BiPermutation Block) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (i : Index) : Block :=
  p.forward (Λ.input compress i (messages i) (salts i))

/-- The digest tape of an honest commitment. -/
def fullLeafDigests (compress : Compression) (p : BiPermutation Block) (message : Message)
    (salts : CompleteSaltTape) : DigestTape :=
  fun i => Λ.digest i (leafReply Λ compress p (messageWords message) salts i)

/-- The honest commitment and proof as a function of the oracle, the message and the salt tape. -/
def mirrorView (build : TranscriptBuilder) : TranscriptView :=
  fun compress p message positions salts =>
    build compress positions (fun index => salts index.val) (fullLeafDigests Λ compress p message salts)

theorem real_planned_leaf_replies {α : Type} (next : List Block → BiPermutation Block → ProbComp α)
    (compress : Compression) (p : BiPermutation Block) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (indices : List Index) (answers : List Block) :
    runPlanned next p answers (leafPlans Λ compress messages salts indices) =
      next ((indices.map (leafReply Λ compress p messages salts)).reverse ++ answers) p := by
  induction indices generalizing answers with
  | nil => rfl
  | cons i rest ih =>
    change runPlanned next p (leafReply Λ compress p messages salts i :: answers)
      (leafPlans Λ compress messages salts rest) = _
    rw [ih]
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem eager_opened_digests (positions : Positions) (compress : Compression) (p : BiPermutation Block)
    (messages : Index → Words 32) (salts : Index → BitVec 128) :
    readOpenedDigests Λ positions (positions.toList.map (leafReply Λ compress p messages salts)) =
      fun i => Λ.digest i.val (leafReply Λ compress p messages salts i.val) := by
  funext i
  unfold readOpenedDigests
  simp only [List.getElem?_map, List.getElem?_idxOf (Finset.mem_toList.mpr i.property), Option.map_some,
    Option.getD_some]

theorem eager_unopened_digests (positions : Positions) (compress : Compression) (p : BiPermutation Block)
    (messages : Index → Words 32) (salts : Index → BitVec 128) :
    unpackDigests Λ positions
      (((hiddenIndices positions).map Subtype.val).map (leafReply Λ compress p messages salts)) =
      fun i => Λ.digest i.val (leafReply Λ compress p messages salts i.val) := by
  funext i
  unfold unpackDigests
  rw [List.map_map]
  have present : i ∈ hiddenIndices positions := by simp [hiddenIndices]
  simp only [List.getElem?_map, List.getElem?_idxOf present, Option.map_some, Option.getD_some,
    Function.comp_apply]

theorem opened_message_same {State : Type} {openingSize : Nat}
    (challenge : Hiding.HidingChallenge State openingSize) (index : {i : Index // i ∈ challenge.positions}) :
    messageWords challenge.message₀ index.val = messageWords challenge.message₁ index.val := by
  have values := congrFun challenge.agree index
  exact congrArg (fun entry : Entry => fun word : Fin 32 => entry.extractLsb' (64 * word.val) 64) values

theorem reunited_digest_tape {State : Type} {openingSize : Nat} (compress : Compression)
    (challenge : Hiding.HidingChallenge State openingSize) (p : BiPermutation Block)
    (openSalts : OpenedSalts challenge.positions) (closedSalts : UnopenedSalts challenge.positions)
    (which : Bool) :
    let m := if which then challenge.message₁ else challenge.message₀
    fullDigestTape (positions := challenge.positions)
      (fun i => Λ.digest i.val (leafReply Λ compress p (messageWords challenge.message₀)
        (publicOpenedSalts openSalts) i.val))
      (fun i => Λ.digest i.val (leafReply Λ compress p (messageWords m) (publicSaltTape closedSalts) i.val)) =
    fun i => Λ.digest i (leafReply Λ compress p (messageWords m) (mergeSaltTape openSalts closedSalts) i) := by
  funext i
  by_cases selected : i ∈ challenge.positions
  · have same := opened_message_same challenge ⟨i, selected⟩
    change messageWords challenge.message₀ i = messageWords challenge.message₁ i at same
    cases which <;>
      simp [fullDigestTape, leafReply, publicOpenedSalts, mergeSaltTape, selected, ← same]
  · simp [fullDigestTape, leafReply, publicSaltTape, mergeSaltTape, selected]

noncomputable def viewReference {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) : ProbComp Output := do
  let permutation ← (PermutationCache.empty Block).sample
  let challenge ← eagerRun compress permutation.val adversary.choose
  let salts ← sampleCompleteSaltTape
  observeTranscriptView adversary (mirrorView Λ build) compress challenge which permutation.val salts

def observeTape {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (challenge : Hiding.HidingChallenge State openingSize)
    (opened : OpenedSalts challenge.positions) (tape : DigestTape) : OracleComp World Output :=
  let (root, proof) := build compress challenge.positions opened tape
  adversary.observe challenge.aux root proof

theorem staged_eager_view {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (challenge : Hiding.HidingChallenge State openingSize) (which : Bool)
    (p : BiPermutation Block) (opened : OpenedSalts challenge.positions)
    (closed : UnopenedSalts challenge.positions) :
    let message := if which then challenge.message₁ else challenge.message₀
    let plans := leafPlans Λ compress (messageWords challenge.message₀) (publicOpenedSalts opened)
      challenge.positions.toList
    let continuation := fun raw p =>
      let openedDigests := readOpenedDigests Λ challenge.positions raw.reverse
      let hiddenPhase := unopenedPlans Λ challenge.positions compress (messageWords message) (publicSaltTape closed)
      runPlanned (fun remaining p => fixedOracleRun (fixedOracle compress p)
        (observeTape adversary build compress challenge opened
          (fullDigestTape openedDigests (unpackDigests Λ challenge.positions remaining.reverse)))) p [] hiddenPhase
    runPlanned continuation p [] plans =
      observeTranscriptView adversary (mirrorView Λ build) compress challenge which p
        (mergeSaltTape opened closed) := by
  dsimp only
  rw [real_planned_leaf_replies]
  simp only [List.append_nil, List.reverse_reverse, eager_opened_digests, unopenedPlans]
  rw [real_planned_leaf_replies]
  simp only [List.append_nil, List.reverse_reverse, eager_unopened_digests, reunited_digest_tape]
  have openCoin : (fun i : {i : Index // i ∈ challenge.positions} => mergeSaltTape opened closed i.val) = opened := by
    funext i
    unfold mergeSaltTape
    exact dite_eq_left i.property
  unfold observeTranscriptView mirrorView fullLeafDigests
  rw [openCoin]
  unfold observeTape
  rfl

theorem eager_reference_equivalence {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) :
    viewReference Λ adversary build compress which =ᵈ
      twoPhaseReference Λ adversary build compress which := by
  let finish := fun challenge p => ($ᵗ CompleteSaltTape) >>=
    observeTranscriptView adversary (mirrorView Λ build) compress challenge which p
  apply (adaptive_posterior_equivalence compress adversary.choose (PermutationCache.empty Block) finish).trans
  unfold twoPhaseReference
  apply EvalDistEq.bind_right
  rintro ⟨challenge, initial⟩
  let message := if which then challenge.message₁ else challenge.message₀
  let plan (opened : OpenedSalts challenge.positions) :=
    leafPlans Λ compress (messageWords challenge.message₀) (publicOpenedSalts opened) challenge.positions.toList
  let closedRun (opened : OpenedSalts challenge.positions) (raw : List Block) (p : BiPermutation Block)
      (closed : UnopenedSalts challenge.positions) :=
    runPlanned (fun remaining p => fixedOracleRun (fixedOracle compress p)
      (observeTape adversary build compress challenge opened
        (fullDigestTape (readOpenedDigests Λ challenge.positions raw.reverse)
          (unpackDigests Λ challenge.positions remaining.reverse)))) p []
      (unopenedPlans Λ challenge.positions compress (messageWords message) (publicSaltTape closed))
  let readOpened (opened : OpenedSalts challenge.positions) (p : Completion initial.entries) :=
    runPlanned (fun raw p => ($ᵗ UnopenedSalts challenge.positions) >>= closedRun opened raw p) p.val []
      (plan opened)
  trans (do let p ← initial.sample
            let opened ← $ᵗ OpenedSalts challenge.positions
            readOpened opened p)
  · apply EvalDistEq.bind_right
    intro p
    dsimp only [finish]
    apply (split_salt_tape challenge.positions
      (observeTranscriptView adversary (mirrorView Λ build) compress challenge which p.val)).trans
    apply EvalDistEq.bind_right
    intro opened
    unfold readOpened
    rw [real_planned_leaf_replies]
    apply EvalDistEq.bind_right
    intro closed
    have same := staged_eager_view Λ adversary build compress challenge which p.val opened closed
    dsimp only at same
    rw [real_planned_leaf_replies] at same
    exact (EvalDistEq.of_evalDist_eq (congrArg evalDist same)).symm
  · apply (EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ OpenedSalts challenge.positions) initial.sample readOpened)).symm.trans
    apply EvalDistEq.bind_right
    intro opened
    apply (prepared_posterior_equivalence
      (fun raw p => ($ᵗ UnopenedSalts challenge.positions) >>= closedRun opened raw p) initial [] (plan opened)).trans
    apply EvalDistEq.bind_right
    rintro ⟨raw, posterior⟩
    have comm := distribution_bind_comm ($ᵗ UnopenedSalts challenge.positions) posterior.sample
      (fun closed p => closedRun opened raw p.val closed)
    exact (EvalDistEq.of_evalDist_eq comm).symm

theorem final_reference_distance {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (budget : Nat) (bounded : Hiding.QueryBound adversary budget) :
    measureETVDist (viewReference Λ adversary build compress false)
      (viewReference Λ adversary build compress true) ≤ mirrorAllowance budget := by
  unfold measureETVDist
  rw [(eager_reference_equivalence Λ adversary build compress false).evalDist_eq,
    (eager_reference_equivalence Λ adversary build compress true).evalDist_eq]
  exact two_phase_reference_distance Λ adversary build compress budget bounded

/-! ### Arithmetic -/

theorem hidden_rate_real_le : hiddenRate.toReal ≤ (1 : ℝ) / 2 ^ 126 := by
  unfold hiddenRate
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_pow]

theorem repeat_allowance_real : repeatAllowance.toReal = (2 : ℝ) ^ 48 / 2 ^ 256 := by
  unfold repeatAllowance
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_pow]

theorem output_allowance_real (budget : Nat) :
    (outputAllowance budget).toReal = 2 ^ 24 * (((budget : ℝ) + 2 ^ 24) / 2 ^ 1600) := by
  unfold outputAllowance
  rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp [ENNReal.toReal_pow]

theorem repeat_allowance_ne_top : repeatAllowance ≠ ⊤ := by
  unfold repeatAllowance
  finiteness

theorem output_allowance_ne_top (budget : Nat) : outputAllowance budget ≠ ⊤ := by
  unfold outputAllowance
  finiteness

theorem mirror_allowance_ne_top (budget : Nat) : mirrorAllowance budget ≠ ⊤ := by
  have rate := hidden_rate_ne_top
  have twice := repeat_allowance_ne_top
  have output := output_allowance_ne_top budget
  unfold mirrorAllowance messageAllowance
  finiteness

theorem message_allowance_real_le (budget : Nat) :
    (messageAllowance budget).toReal ≤
      (2 : ℝ) ^ 48 / 2 ^ 256 + ((budget : ℝ) / 2 ^ 126 + (budget : ℝ) / 2 ^ 126) +
        2 ^ 24 * (((budget : ℝ) + 2 ^ 24) / 2 ^ 1600) := by
  have nonnegative : 0 ≤ (budget : ℝ) := by positivity
  have term : ((budget : ENNReal) * hiddenRate).toReal ≤ (budget : ℝ) / 2 ^ 126 := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    exact (mul_le_mul_of_nonneg_left hidden_rate_real_le nonnegative).trans_eq (by ring)
  unfold messageAllowance
  refine ENNReal.toReal_add_le.trans (add_le_add (ENNReal.toReal_add_le.trans (add_le_add
    repeat_allowance_real.le (ENNReal.toReal_add_le.trans (add_le_add term term))))
    (output_allowance_real budget).le)

theorem mirror_allowance_real_le (budget : Nat) :
    (mirrorAllowance budget).toReal ≤ ((budget : ℝ) + 1) / 2 ^ 120 := by
  have nonnegative : 0 ≤ (budget : ℝ) := by positivity
  have message := message_allowance_real_le budget
  have twice := repeat_allowance_real
  have total : (mirrorAllowance budget).toReal ≤
      ((messageAllowance budget).toReal + (messageAllowance budget).toReal) +
        (repeatAllowance.toReal + repeatAllowance.toReal) := by
    unfold mirrorAllowance
    exact ENNReal.toReal_add_le.trans (add_le_add ENNReal.toReal_add_le ENNReal.toReal_add_le)
  refine total.trans ?_
  rw [twice]
  refine (add_le_add (add_le_add message message) le_rfl).trans ?_
  norm_num
  linarith

/-- **The reference experiment hides**, for every fixed compression function. -/
theorem final_reference_hiding {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (budget : Nat) (bounded : Hiding.QueryBound adversary budget) :
    measureTVDist (viewReference Λ adversary build compress false)
      (viewReference Λ adversary build compress true) ≤ min 1 (((budget : ℝ) + 1) / 2 ^ 120) := by
  refine le_min (measureTVDist_le_one _ _) ?_
  rw [measureTVDist_eq_toReal_measureETVDist]
  exact (ENNReal.toReal_mono (mirror_allowance_ne_top budget)
    (final_reference_distance Λ adversary build compress budget bounded)).trans
    (mirror_allowance_real_le budget)

end TwoPermutationPrototype.Sampling.Mirror
