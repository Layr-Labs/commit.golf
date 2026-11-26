import CommitGolfCandidate.C3HidingConditional
import CommitGolfCandidate.TwoPermutationHidingBridge

/-! # Hiding for the 3c1p leaf: from the contract's game to the conditional game

The reference experiment samples a full permutation, runs the adversary's first stage on it,
draws the salt tape and shows the honest transcript of `c3HonestView`. Lazily sampling the
permutation (`adaptive_posterior_equivalence`) and moving the opened leaves' calls ahead of the
unopened ones turns it into `c3TwoPhaseReference`, whose two worlds are close by
`c3_two_phase_reference_hiding`. `scheme_hiding_of_c3_transcript` is the contract's hiding
clause for any scheme whose executable transcript refines `c3HonestView`. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048
set_option autoImplicit false

noncomputable local instance c3EagerFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

local instance c3EagerDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

def c3LeafReply (compress : Compression) (p : BiPermutation Block) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (i : Index) : Block :=
  p.forward (c3HiddenInput compress i (messages i) (salts i))

theorem c3_full_leaf_digests_reply (compress : Compression) (p : BiPermutation Block) (message : Message)
    (salts : CompleteSaltTape) :
    c3FullLeafDigests compress p message salts =
      fun i => outputDigest (c3LeafReply compress p (messageWords message) salts i) := rfl

theorem c3_real_planned_leaf_replies {α : Type} (next : List Block → BiPermutation Block → ProbComp α)
    (compress : Compression) (p : BiPermutation Block) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (indices : List Index) (answers : List Block) :
    runPlanned next p answers (c3LeafPlans compress messages salts indices) =
      next ((indices.map (c3LeafReply compress p messages salts)).reverse ++ answers) p := by
  induction indices generalizing answers with
  | nil => rfl
  | cons i rest ih =>
    change runPlanned next p (c3LeafReply compress p messages salts i :: answers)
      (c3LeafPlans compress messages salts rest) = _
    rw [ih]
    simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem c3_eager_opened_digests (positions : Positions) (compress : Compression) (p : BiPermutation Block)
    (messages : Index → Words 32) (salts : Index → BitVec 128) :
    c3ReadOpenedDigests positions (positions.toList.map (c3LeafReply compress p messages salts)) =
      fun i => outputDigest (c3LeafReply compress p messages salts i.val) := by
  funext i
  unfold c3ReadOpenedDigests
  rw [List.map_map]
  simp only [List.getElem?_map, List.getElem?_idxOf (Finset.mem_toList.mpr i.property), Option.map_some,
    Option.getD_some, Function.comp_apply]

theorem c3_eager_unopened_digests (positions : Positions) (compress : Compression) (p : BiPermutation Block)
    (messages : Index → Words 32) (salts : Index → BitVec 128) :
    c3UnpackDigests positions
      (((hiddenIndices positions).map Subtype.val).map (c3LeafReply compress p messages salts)) =
      fun i => outputDigest (c3LeafReply compress p messages salts i.val) := by
  funext i
  unfold c3UnpackDigests
  rw [List.map_map, List.map_map]
  have present : i ∈ hiddenIndices positions := by simp [hiddenIndices]
  simp only [List.getElem?_map, List.getElem?_idxOf present, Option.map_some, Option.getD_some,
    Function.comp_apply]

private theorem c3_opened_message_same {State : Type} {openingSize : Nat}
    (challenge : Hiding.HidingChallenge State openingSize) (index : {i : Index // i ∈ challenge.positions}) :
    messageWords challenge.message₀ index.val = messageWords challenge.message₁ index.val := by
  have values := congrFun challenge.agree index
  exact congrArg (fun entry : Entry => fun word : Fin 32 => entry.extractLsb' (64 * word.val) 64) values

theorem c3_reunited_digest_tape {State : Type} {openingSize : Nat} (compress : Compression)
    (challenge : Hiding.HidingChallenge State openingSize) (p : BiPermutation Block)
    (openSalts : OpenedSalts challenge.positions) (closedSalts : UnopenedSalts challenge.positions)
    (which : Bool) :
    let m := if which then challenge.message₁ else challenge.message₀
    fullDigestTape (positions := challenge.positions)
      (fun i => outputDigest (c3LeafReply compress p (messageWords challenge.message₀)
        (publicOpenedSalts openSalts) i.val))
      (fun i => outputDigest (c3LeafReply compress p (messageWords m) (publicSaltTape closedSalts) i.val)) =
    fun i => outputDigest (c3LeafReply compress p (messageWords m) (mergeSaltTape openSalts closedSalts) i) := by
  funext i
  by_cases selected : i ∈ challenge.positions
  · have same := c3_opened_message_same challenge ⟨i, selected⟩
    change messageWords challenge.message₀ i = messageWords challenge.message₁ i at same
    cases which <;>
      simp [fullDigestTape, c3LeafReply, publicOpenedSalts, mergeSaltTape, selected, ← same]
  · simp [fullDigestTape, c3LeafReply, publicSaltTape, mergeSaltTape, selected]

noncomputable def c3ViewReference {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) : ProbComp Output := do
  let permutation ← (PermutationCache.empty Block).sample
  let challenge ← eagerRun compress permutation.val adversary.choose
  let salts ← sampleCompleteSaltTape
  observeTranscriptView adversary (c3HonestView build) compress challenge which permutation.val salts

private def c3ObserveTape {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (challenge : Hiding.HidingChallenge State openingSize)
    (opened : OpenedSalts challenge.positions) (tape : DigestTape) : OracleComp World Output :=
  let (root, proof) := build compress challenge.positions opened tape
  adversary.observe challenge.aux root proof

private theorem c3_staged_eager_view {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (challenge : Hiding.HidingChallenge State openingSize) (which : Bool)
    (p : BiPermutation Block) (opened : OpenedSalts challenge.positions)
    (closed : UnopenedSalts challenge.positions) :
    let message := if which then challenge.message₁ else challenge.message₀
    let plans := c3LeafPlans compress (messageWords challenge.message₀) (publicOpenedSalts opened)
      challenge.positions.toList
    let continuation := fun raw p =>
      let openedDigests := c3ReadOpenedDigests challenge.positions raw.reverse
      let hiddenPhase := c3UnopenedPlans challenge.positions compress (messageWords message) (publicSaltTape closed)
      runPlanned (fun remaining p => fixedOracleRun (fixedOracle compress p)
        (c3ObserveTape adversary build compress challenge opened
          (fullDigestTape openedDigests (c3UnpackDigests challenge.positions remaining.reverse)))) p [] hiddenPhase
    runPlanned continuation p [] plans =
      observeTranscriptView adversary (c3HonestView build) compress challenge which p
        (mergeSaltTape opened closed) := by
  dsimp only
  rw [c3_real_planned_leaf_replies]
  simp only [List.append_nil, List.reverse_reverse, c3_eager_opened_digests, c3UnopenedPlans]
  rw [c3_real_planned_leaf_replies]
  simp only [List.append_nil, List.reverse_reverse, c3_eager_unopened_digests, c3_reunited_digest_tape]
  have openCoin : (fun i : {i : Index // i ∈ challenge.positions} => mergeSaltTape opened closed i.val) = opened := by
    funext i
    unfold mergeSaltTape
    exact dite_eq_left i.property
  unfold observeTranscriptView c3HonestView
  rw [openCoin]
  unfold c3ObserveTape
  rfl

theorem c3_eager_reference_equivalence {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (which : Bool) :
    c3ViewReference adversary build compress which =ᵈ
      c3TwoPhaseReference adversary build compress which := by
  let finish := fun challenge p => ($ᵗ CompleteSaltTape) >>=
    observeTranscriptView adversary (c3HonestView build) compress challenge which p
  apply (adaptive_posterior_equivalence compress adversary.choose (PermutationCache.empty Block) finish).trans
  unfold c3TwoPhaseReference
  apply EvalDistEq.bind_right
  rintro ⟨challenge, initial⟩
  let message := if which then challenge.message₁ else challenge.message₀
  let plan (opened : OpenedSalts challenge.positions) :=
    c3LeafPlans compress (messageWords challenge.message₀) (publicOpenedSalts opened) challenge.positions.toList
  let closedRun (opened : OpenedSalts challenge.positions) (raw : List Block) (p : BiPermutation Block)
      (closed : UnopenedSalts challenge.positions) :=
    runPlanned (fun remaining p => fixedOracleRun (fixedOracle compress p)
      (c3ObserveTape adversary build compress challenge opened
        (fullDigestTape (c3ReadOpenedDigests challenge.positions raw.reverse)
          (c3UnpackDigests challenge.positions remaining.reverse)))) p []
      (c3UnopenedPlans challenge.positions compress (messageWords message) (publicSaltTape closed))
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
      (observeTranscriptView adversary (c3HonestView build) compress challenge which p.val)).trans
    apply EvalDistEq.bind_right
    intro opened
    unfold readOpened
    rw [c3_real_planned_leaf_replies]
    apply EvalDistEq.bind_right
    intro closed
    have same := c3_staged_eager_view adversary build compress challenge which p.val opened closed
    dsimp only at same
    rw [c3_real_planned_leaf_replies] at same
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

theorem c3_final_reference_hiding {State Output : Type} {openingSize : Nat}
    (adversary : Hiding.HidingAdversary State Output openingSize) (build : TranscriptBuilder)
    (compress : Compression) (budget : Nat) (bounded : Hiding.QueryBound adversary budget) :
    measureTVDist (c3ViewReference adversary build compress false)
      (c3ViewReference adversary build compress true) ≤ min 1 (((budget : ℝ) + 1) / 2 ^ 120) := by
  unfold measureTVDist
  rw [(c3_eager_reference_equivalence adversary build compress false).evalDist_eq,
    (c3_eager_reference_equivalence adversary build compress true).evalDist_eq]
  exact c3_two_phase_reference_hiding adversary build compress budget bounded

end TwoPermutationPrototype.Sampling
