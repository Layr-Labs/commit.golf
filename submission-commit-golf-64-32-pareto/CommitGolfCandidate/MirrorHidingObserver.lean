import CommitGolfCandidate.MirrorHidingCoincide

/-! # Hiding for a mirrored leaf: observer hits and honest proposals

Counterpart of `C3HidingObserver`. The observer's trace hits a hidden row with probability at
most `hiddenRate` per query, and the honest plans of the unopened leaves read their private
tape, with the digest window chosen by position.

The conflict bound changes. `honest_proposal_conflict_le` no longer takes tags of the opened rows
and no longer needs distinct honest inputs. Off the event `bad` (two unopened inputs equal, or an
unopened input already in the cache) the proposals conflict only through the output birthday
term. The event itself is charged to the unopened salts: first-stage rows at `2/2^128` each,
`repeatAllowance` for two unopened leaves, and `openedHit` for the opened rows. -/
namespace TwoPermutationPrototype.Sampling.Mirror
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option exponentiation.threshold 2048
set_option autoImplicit false

local instance observerDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

noncomputable local instance observerFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

variable (Λ : MirrorLayout)

def hiddenRowsFor {positions : Positions} (compress : Compression) (digests : DigestTape)
    (messages : Index → Words 32) (hidden : KeyTape positions)
    (indices : List (HiddenIndex positions)) : List Row :=
  indices.map (fun index => hiddenRow Λ compress digests messages index.val (hidden index))

noncomputable def hiddenRows {positions : Positions} (compress : Compression) (digests : DigestTape)
    (messages : Index → Words 32) (hidden : KeyTape positions) : List Row :=
  hiddenRowsFor Λ compress digests messages hidden (hiddenIndices positions)

theorem rowHits_hidden_iff {positions : Positions} (compress : Compression) (digests : DigestTape)
    (messages : Index → Words 32) (hidden : KeyTape positions) (query : Row) :
    rowHits (hiddenRows Λ compress digests messages hidden) query = true ↔
      HitsHidden Λ compress digests messages query hidden := by
  classical
  simp only [rowHits, List.any_eq_true, hiddenRows, hiddenRowsFor, hiddenIndices, List.mem_map,
    Finset.mem_toList, Finset.mem_univ, true_and, decide_eq_true_eq, HitsHidden]
  constructor
  · rintro ⟨row, ⟨i, rfl⟩, input | output⟩
    · exact Or.inl ⟨i, input.symm⟩
    · exact Or.inr ⟨i, output.symm⟩
  · rintro (⟨i, input⟩ | ⟨i, output⟩)
    · exact ⟨_, ⟨i, rfl⟩, Or.inl input.symm⟩
    · exact ⟨_, ⟨i, rfl⟩, Or.inr output.symm⟩

theorem independent_hidden_observer_hits (positions : Positions) (digests : DigestTape)
    (messages : Index → Words 32) (compress : Compression) (p : BiPermutation Block)
    {α : Type} (observer : OracleComp World α) (budget : Nat) (bounded : QueryBounded observer budget) :
    Pr{let result ← (do let hidden ← sampleKeyTape positions
                        let rows := hiddenRows Λ compress digests messages hidden
                        flaggedRun (fixedOracle compress p) (marksReferencePair p rows) observer)}[
      result.2.2 = true] ≤ (budget : ENNReal) * hiddenRate := by
  classical
  let oracle := fixedOracle compress p
  let traced := fixedOracleRun oracle (tracePermutation observer)
  let flag (hidden : KeyTape positions) (result : α × List Row) : α × Unit × Bool :=
    (result.1, (), result.2.any (rowHits (hiddenRows Λ compress digests messages hidden)))
  have reordered := EvalDistEq.of_evalDist_eq
    (distribution_bind_comm (sampleKeyTape positions) traced (fun hidden result => pure (flag hidden result)))
  have eventEqual := reordered.prEvent_eq (fun flagged => flagged.2.2 = true)
  have expand (hidden : KeyTape positions) :
      flaggedRun oracle (marksReferencePair p (hiddenRows Λ compress digests messages hidden)) observer =
        traced >>= fun result => pure (flag hidden result) := by
    unfold oracle traced flag
    rw [flagged_reference_trace]
    simp only [Bool.false_or, map_eq_bind_pure_comp]
    rfl
  simp only [← show oracle = fixedOracle compress p from rfl, expand]
  rw [eventEqual]
  apply prEvent_bind_le_of_forall_le_of_support
  intro result present
  simp only [bind_pure_comp, prEvent_map, flag, List.any_eq_true, rowHits_hidden_iff]
  have cost := fixed_reference_trace_hit_le Λ positions compress digests messages result.2
  refine cost.trans (mul_le_mul_of_nonneg_right ?_ zero_le)
  exact_mod_cast trace_permutation_length oracle observer budget bounded result present

theorem independent_hidden_observer_distance (positions : Positions) (digests : DigestTape)
    (messages : Index → Words 32) (compress : Compression) (p : BiPermutation Block)
    {α : Type} (observer : OracleComp World α) (budget : Nat) (bounded : QueryBounded observer budget) :
    measureTVDist
      (sampleKeyTape positions >>= fun _ => fixedOracleRun (fixedOracle compress p) observer)
      (sampleKeyTape positions >>= fun hidden => fixedOracleRun
        (fixedOracle compress (p.programRows (hiddenRows Λ compress digests messages hidden))) observer) ≤
      ((budget : ENNReal) * hiddenRate).toReal := by
  classical
  refine (distance_bind_le_averaged_bad (sampleKeyTape positions) _ _
    (fun hidden => flaggedRun (fixedOracle compress p)
      (marksReferencePair p (hiddenRows Λ compress digests messages hidden)) observer)
    (fun hidden => programming_distance_le_reference_hit compress p
      (hiddenRows Λ compress digests messages hidden) observer)).trans ?_
  exact ENNReal.toReal_mono (by unfold hiddenRate; finiteness)
    (independent_hidden_observer_hits Λ positions digests messages compress p observer budget bounded)

/-! ### Alignment of the honest plans with the private tape -/

def hiddenSalts {positions : Positions} (hidden : KeyTape positions) (index : Index) : BitVec 128 :=
  if closed : index ∉ positions then (hidden ⟨index, closed⟩).1 else 0

def hiddenReply {positions : Positions} (digests : DigestTape) (hidden : KeyTape positions)
    (index : HiddenIndex positions) : Block :=
  Λ.reply index.val (digests index.val) (hidden index).2

theorem hidden_rows_match_plans {positions : Positions} (compress : Compression) (digests : DigestTape)
    (messages : Index → Words 32) (hidden : KeyTape positions)
    (indices : List (HiddenIndex positions)) (answers : List Block) :
    plannedRows answers (leafPlans Λ compress messages (hiddenSalts hidden) (indices.map Subtype.val))
      (indices.map (hiddenReply Λ digests hidden)) =
      hiddenRowsFor Λ compress digests messages hidden indices := by
  induction indices generalizing answers with
  | nil => rfl
  | cons index rest ih =>
    have salt : hiddenSalts hidden index.val = (hidden index).1 := by
      unfold hiddenSalts
      exact dite_eq_left index.property
    change (Λ.input compress index.val (messages index.val) (hiddenSalts hidden index.val),
        Λ.reply index.val (digests index.val) (hidden index).2) ::
      plannedRows ((Λ.reply index.val (digests index.val) (hidden index).2) :: answers)
        (leafPlans Λ compress messages (hiddenSalts hidden) (rest.map Subtype.val))
        (rest.map (hiddenReply Λ digests hidden)) =
      hiddenRow Λ compress digests messages index.val (hidden index) ::
        hiddenRowsFor Λ compress digests messages hidden rest
    rw [salt, ih]
    rfl

/-! ### Honest proposals -/

theorem independent_honest_proposals {α : Type} (positions : Positions) (opened : OpenedDigests positions)
    (next : (Index → BitVec 128) → List Block → ProbComp α) :
    (do let salts ← $ᵗ UnopenedSalts positions
        let tape ← sampleProposalTape (hiddenIndices positions).length
        next (publicSaltTape salts) tape) =ᵈ
      (do let digests ← $ᵗ UnopenedDigestTape positions
          let hidden ← sampleKeyTape positions
          next (hiddenSalts hidden)
            ((hiddenIndices positions).map (hiddenReply Λ (fullDigestTape opened digests) hidden))) := by
  classical
  let indices := hiddenIndices positions
  let paired (salts : UnopenedSalts positions) (replies : HiddenIndex positions → Block) :=
    next (publicSaltTape salts) (indices.map replies)
  trans (do let salts ← $ᵗ UnopenedSalts positions
            let replies ← $ᵗ (HiddenIndex positions → Block)
            paired salts replies)
  · apply EvalDistEq.bind_right
    intro salts
    exact (uniform_enum_block_tape indices (Finset.nodup_toList _)
      (fun i => by simp [indices, hiddenIndices]) (next (publicSaltTape salts))).symm
  · let combine := functionPairEquiv (HiddenIndex positions) (BitVec 128) Block
    trans (do let raw ← $ᵗ RawTape positions
              paired (combine raw).1 (combine raw).2)
    · have same := uniform_transport_bind (transportOfEquiv combine.symm)
        (fun pair => paired pair.1 pair.2)
      rw [SampleableType.uniformSample_prod_eq_bind] at same
      simp only [bind_assoc, pure_bind] at same
      exact same
    · let fromSecret (digests : UnopenedDigestTape positions) (hidden : KeyTape positions) :=
        next (hiddenSalts hidden) (indices.map (hiddenReply Λ (fullDigestTape opened digests) hidden))
      trans (do let raw ← $ᵗ RawTape positions
                let pieces := factorReplies Λ positions raw
                fromSecret pieces.1 pieces.2)
      · apply EvalDistEq.bind_right
        intro raw
        dsimp only [paired, fromSecret]
        have sameSalts : publicSaltTape (combine raw).1 = hiddenSalts (factorReplies Λ positions raw).2 := by
          funext i
          unfold publicSaltTape hiddenSalts
          split <;> rfl
        have sameReplies : (combine raw).2 =
            hiddenReply Λ (fullDigestTape opened (factorReplies Λ positions raw).1)
              (factorReplies Λ positions raw).2 := by
          funext i
          have closed := i.property
          simp only [hiddenReply, fullDigestTape, closed, dite_false]
          change (raw i).2 = (Λ.split i.val).symm ((Λ.split i.val (raw i).2).1, (Λ.split i.val (raw i).2).2)
          simp
        rw [sameSalts, sameReplies]
      · exact expose_unopened_digests Λ positions fromSecret

noncomputable def unopenedPlans (positions : Positions) (compress : Compression)
    (messages : Index → Words 32) (salts : Index → BitVec 128) : List InputPlan :=
  leafPlans Λ compress messages salts ((hiddenIndices positions).map Subtype.val)

/-- The chance, over the unopened salts, that an unopened input equals the input of one of the
given rows. For the opened rows it is averaged over the opened salts later. -/
noncomputable def openedHit (positions : Positions) (compress : Compression)
    (messages : Index → Words 32) (rows : List Row) : ENNReal :=
  Pr{let salts ← $ᵗ UnopenedSalts positions}[
    ∃ j : HiddenIndex positions, ∃ row ∈ rows,
      row.1 = Λ.input compress j.val (messages j.val) (salts j)]

/-- The inputs of the unopened plans are the unopened inputs. -/
theorem unopened_plan_inputs (positions : Positions) (compress : Compression)
    (messages : Index → Words 32) (salts : UnopenedSalts positions) (tape : List Block)
    (length : tape.length = (hiddenIndices positions).length) :
    (plannedRows [] (unopenedPlans Λ positions compress messages (publicSaltTape salts)) tape).map
        Prod.fst = hiddenInputs Λ positions compress messages salts := by
  unfold unopenedPlans hiddenInputs
  rw [leaf_plan_inputs Λ compress messages (publicSaltTape salts) _ [] tape (by simpa using length),
    List.map_map]
  refine List.map_congr_left fun j _ => ?_
  have salt : publicSaltTape salts j.val = salts j := by
    unfold publicSaltTape
    exact dite_eq_left j.property
  simp only [Function.comp_apply, salt]

/-- **The honest proposals rarely conflict.** Replaces `c3_honest_proposal_conflict_le`: no tags
of the opened rows, no distinct inputs. -/
theorem honest_proposal_conflict_le {positions : Positions} (cache : Cache) (compress : Compression)
    (messages : Index → Words 32) (firstStage openedRows : List Row) (budget : Nat)
    (seed : cache.entries = openedRows ++ firstStage) (firstCount : firstStage.length ≤ budget)
    (openedCount : openedRows.length ≤ positions.card) :
    Pr{let flag ← (($ᵗ UnopenedSalts positions) >>= fun salts =>
      proposedConflict cache [] (unopenedPlans Λ positions compress messages (publicSaltTape salts)))}[
      flag = true] ≤
      (repeatAllowance + ((budget : ENNReal) * hiddenRate + openedHit Λ positions compress messages openedRows)) +
        (2 ^ 24 : ENNReal) * (((budget : ENNReal) + 2 ^ 24) / 2 ^ 1600) := by
  classical
  let indices := hiddenIndices positions
  let count := indices.length
  let plan (salts : UnopenedSalts positions) :=
    unopenedPlans Λ positions compress messages (publicSaltTape salts)
  let outputAllowance := (2 ^ 24 : ENNReal) * (((budget : ENNReal) + 2 ^ 24) / 2 ^ 1600)
  have lengthOf (salts : UnopenedSalts positions) : (plan salts).length = count := by
    simp [plan, count, indices, unopenedPlans, leaf_plans_length]
  have total := hidden_index_count positions
  have plansBound : count ≤ 2 ^ 24 := by dsimp [count, indices]; omega
  have withReplies : cache.entries.length + count ≤ budget + 2 ^ 24 := by
    rw [seed, List.length_append]
    dsimp [count, indices]
    omega
  have outputBound (salts : UnopenedSalts positions) :
      ((plan salts).length : ENNReal) * (((cache.entries.length + (plan salts).length : Nat) : ENNReal) / 2 ^ 1600) ≤
        outputAllowance := by
    rw [lengthOf]
    unfold outputAllowance
    apply mul_le_mul
    · exact_mod_cast plansBound
    · apply ENNReal.div_le_div_right
      exact_mod_cast withReplies
    · exact zero_le
    · exact zero_le
  let inputOf (salts : UnopenedSalts positions) (j : HiddenIndex positions) : Block :=
    Λ.input compress j.val (messages j.val) (salts j)
  let bad (salts : UnopenedSalts positions) : Prop :=
    ¬ (hiddenInputs Λ positions compress messages salts).Nodup ∨
      ∃ j : HiddenIndex positions, ¬ UnusedInput cache.entries (inputOf salts j)
  have clean (salts : UnopenedSalts positions) (_ : salts ∈ support ($ᵗ UnopenedSalts positions))
      (good : ¬ bad salts) :
      Pr{let flag ← proposedConflict cache [] (plan salts)}[flag = true] ≤ outputAllowance := by
    have nodup : (hiddenInputs Λ positions compress messages salts).Nodup :=
      not_not.mp (fun repeated => good (Or.inl repeated))
    have unused (j : HiddenIndex positions) : UnusedInput cache.entries (inputOf salts j) :=
      not_not.mp (fun used => good (Or.inr ⟨j, used⟩))
    have inputs (tape : List Block) (possible : tape ∈ support (sampleProposalTape (plan salts).length)) :
        (plannedRows [] (plan salts) tape).map Prod.fst =
          hiddenInputs Λ positions compress messages salts :=
      unopened_plan_inputs Λ positions compress messages salts tape
        ((sampleProposalTape_length possible).trans (lengthOf salts))
    have proposed := proposal_conflict_decompose cache [] (plan salts)
      (fun tape possible => (inputs tape possible).symm ▸ nodup)
    have noHit : Pr{let tape ← sampleProposalTape (plan salts).length}[
        plannedInputHit cache.entries [] (plan salts) tape] = 0 := by
      apply prEvent_eq_zero_of_forall_mem_support
      rintro tape possible ⟨row, present, used⟩
      have member : row.1 ∈ (plannedRows [] (plan salts) tape).map Prod.fst :=
        List.mem_map.mpr ⟨row, present, rfl⟩
      rw [inputs tape possible] at member
      obtain ⟨j, _, equal⟩ := List.mem_map.mp member
      exact used (equal ▸ unused j)
    rw [noHit, zero_add] at proposed
    exact proposed.trans (outputBound salts)
  have split := prEvent_bind_le_prEvent_add_of_support ($ᵗ UnopenedSalts positions)
    (fun salts => proposedConflict cache [] (plan salts)) bad (· = true) clean
  refine split.trans (add_le_add ?_ le_rfl)
  let sample : ProbComp (UnopenedSalts positions) := $ᵗ UnopenedSalts positions
  let repeated (salts : UnopenedSalts positions) : Prop :=
    ¬ (hiddenInputs Λ positions compress messages salts).Nodup
  let early (salts : UnopenedSalts positions) : Prop :=
    ∃ old ∈ firstStage, ∃ j : HiddenIndex positions, inputOf salts j = old.1
  let shown (salts : UnopenedSalts positions) : Prop :=
    ∃ j : HiddenIndex positions, ∃ row ∈ openedRows, row.1 = inputOf salts j
  have earlyBound : Pr{let salts ← sample}[early salts] ≤ (budget : ENNReal) * hiddenRate := by
    have perRow := prEvent_list_le firstStage sample
      (fun old salts => ∃ j : HiddenIndex positions, inputOf salts j = old.1)
      ((1 : ENNReal) / 2 ^ 128 + 1 / 2 ^ 128)
      (fun old _ => salts_input_guess_le Λ positions compress messages old.1)
    refine perRow.trans (mul_le_mul' (by exact_mod_cast firstCount) ?_)
    unfold hiddenRate
    exact le_self_add
  refine (prEvent_mono sample _ (fun salts => repeated salts ∨ (early salts ∨ shown salts)) ?_).trans
    ((prEvent_or_le sample _ _).trans (add_le_add
      (hidden_inputs_repeat_le Λ positions compress messages)
      ((prEvent_or_le sample _ _).trans (add_le_add earlyBound le_rfl))))
  rintro salts (twice | ⟨j, used⟩)
  · exact Or.inl twice
  · have found : ∃ old ∈ openedRows ++ firstStage, old.1 = inputOf salts j := by
      simpa [UnusedInput, seed] using used
    obtain ⟨old, member, equal⟩ := found
    rcases List.mem_append.mp member with opened | first
    · exact Or.inr (Or.inr ⟨j, old, opened, equal⟩)
    · exact Or.inr (Or.inl ⟨old, first, j, equal.symm⟩)

end TwoPermutationPrototype.Sampling.Mirror
