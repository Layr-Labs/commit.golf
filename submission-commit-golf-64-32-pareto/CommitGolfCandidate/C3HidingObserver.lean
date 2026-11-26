import CommitGolfCandidate.C3HidingCore
import CommitGolfCandidate.TwoPermutationHidingIndependent

/-! # Hiding for the 3c1p leaf: observer hits and honest proposals

One-row counterparts of the leader's `TwoPermutationHidingObserver`, `Alignment` and
`Independent`: the observer's trace hits a hidden row with probability at most
`c3HiddenRate` per query, the honest plans of the unopened leaves read their private tape, and
the honest proposals conflict with the first-stage cache or with each other only rarely. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option autoImplicit false

local instance c3ObserverDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

noncomputable local instance c3ObserverFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

def c3HiddenRowsFor {positions : Positions} (compress : Compression) (digests : DigestTape)
    (messages : Index → Words 32) (hidden : C3HiddenTape positions)
    (indices : List (HiddenIndex positions)) : List Row :=
  indices.map (fun index => c3HiddenRow compress digests messages index.val (hidden index))

noncomputable def c3HiddenRows {positions : Positions} (compress : Compression) (digests : DigestTape)
    (messages : Index → Words 32) (hidden : C3HiddenTape positions) : List Row :=
  c3HiddenRowsFor compress digests messages hidden (hiddenIndices positions)

private theorem c3_rowHits_hidden_iff {positions : Positions} (compress : Compression) (digests : DigestTape)
    (messages : Index → Words 32) (hidden : C3HiddenTape positions) (query : Row) :
    rowHits (c3HiddenRows compress digests messages hidden) query = true ↔
      c3HitsHidden compress digests messages query hidden := by
  classical
  simp only [rowHits, List.any_eq_true, c3HiddenRows, c3HiddenRowsFor, hiddenIndices, List.mem_map,
    Finset.mem_toList, Finset.mem_univ, true_and, decide_eq_true_eq, c3HitsHidden]
  constructor
  · rintro ⟨row, ⟨i, rfl⟩, input | output⟩
    · exact Or.inl ⟨i, input.symm⟩
    · exact Or.inr ⟨i, output.symm⟩
  · rintro (⟨i, input⟩ | ⟨i, output⟩)
    · exact ⟨_, ⟨i, rfl⟩, Or.inl input.symm⟩
    · exact ⟨_, ⟨i, rfl⟩, Or.inr output.symm⟩

theorem c3_independent_hidden_observer_hits (positions : Positions) (digests : DigestTape)
    (messages : Index → Words 32) (compress : Compression) (p : BiPermutation Block)
    {α : Type} (observer : OracleComp World α) (budget : Nat) (bounded : QueryBounded observer budget) :
    Pr{let result ← (do let hidden ← sampleC3HiddenTape positions
                        let rows := c3HiddenRows compress digests messages hidden
                        flaggedRun (fixedOracle compress p) (marksReferencePair p rows) observer)}[
      result.2.2 = true] ≤ (budget : ENNReal) * c3HiddenRate := by
  classical
  let oracle := fixedOracle compress p
  let traced := fixedOracleRun oracle (tracePermutation observer)
  let flag (hidden : C3HiddenTape positions) (result : α × List Row) : α × Unit × Bool :=
    (result.1, (), result.2.any (rowHits (c3HiddenRows compress digests messages hidden)))
  have reordered := EvalDistEq.of_evalDist_eq
    (distribution_bind_comm (sampleC3HiddenTape positions) traced (fun hidden result => pure (flag hidden result)))
  have eventEqual := reordered.prEvent_eq (fun flagged => flagged.2.2 = true)
  have expand (hidden : C3HiddenTape positions) :
      flaggedRun oracle (marksReferencePair p (c3HiddenRows compress digests messages hidden)) observer =
        traced >>= fun result => pure (flag hidden result) := by
    unfold oracle traced flag
    rw [flagged_reference_trace]
    simp only [Bool.false_or, map_eq_bind_pure_comp]
    rfl
  simp only [← show oracle = fixedOracle compress p from rfl, expand]
  rw [eventEqual]
  apply prEvent_bind_le_of_forall_le_of_support
  intro result present
  simp only [bind_pure_comp, prEvent_map, flag, List.any_eq_true, c3_rowHits_hidden_iff]
  have cost := c3_fixed_reference_trace_hit_le positions compress digests messages result.2
  refine cost.trans (mul_le_mul_of_nonneg_right ?_ zero_le)
  exact_mod_cast trace_permutation_length oracle observer budget bounded result present

theorem c3_independent_hidden_observer_distance (positions : Positions) (digests : DigestTape)
    (messages : Index → Words 32) (compress : Compression) (p : BiPermutation Block)
    {α : Type} (observer : OracleComp World α) (budget : Nat) (bounded : QueryBounded observer budget) :
    measureTVDist
      (sampleC3HiddenTape positions >>= fun _ => fixedOracleRun (fixedOracle compress p) observer)
      (sampleC3HiddenTape positions >>= fun hidden => fixedOracleRun
        (fixedOracle compress (p.programRows (c3HiddenRows compress digests messages hidden))) observer) ≤
      ((budget : ENNReal) * c3HiddenRate).toReal := by
  classical
  refine (distance_bind_le_averaged_bad (sampleC3HiddenTape positions) _ _
    (fun hidden => flaggedRun (fixedOracle compress p)
      (marksReferencePair p (c3HiddenRows compress digests messages hidden)) observer)
    (fun hidden => programming_distance_le_reference_hit compress p
      (c3HiddenRows compress digests messages hidden) observer)).trans ?_
  exact ENNReal.toReal_mono (by unfold c3HiddenRate; finiteness)
    (c3_independent_hidden_observer_hits positions digests messages compress p observer budget bounded)

/-! ### Alignment of the honest plans with the private tape -/

def c3HiddenSalts {positions : Positions} (hidden : C3HiddenTape positions) (index : Index) : BitVec 128 :=
  if closed : index ∉ positions then (hidden ⟨index, closed⟩).1 else 0

def c3HiddenReply {positions : Positions} (digests : DigestTape) (hidden : C3HiddenTape positions)
    (index : HiddenIndex positions) : Block :=
  (hidden index).2 ++ digests index.val

theorem c3_hidden_rows_match_plans {positions : Positions} (compress : Compression) (digests : DigestTape)
    (messages : Index → Words 32) (hidden : C3HiddenTape positions)
    (indices : List (HiddenIndex positions)) (answers : List Block) :
    plannedRows answers (c3LeafPlans compress messages (c3HiddenSalts hidden) (indices.map Subtype.val))
      (indices.map (c3HiddenReply digests hidden)) =
      c3HiddenRowsFor compress digests messages hidden indices := by
  induction indices generalizing answers with
  | nil => rfl
  | cons index rest ih =>
    have salt : c3HiddenSalts hidden index.val = (hidden index).1 := by
      unfold c3HiddenSalts
      exact dite_eq_left index.property
    change (c3HiddenInput compress index.val (messages index.val) (c3HiddenSalts hidden index.val),
        (hidden index).2 ++ digests index.val) ::
      plannedRows (((hidden index).2 ++ digests index.val) :: answers)
        (c3LeafPlans compress messages (c3HiddenSalts hidden) (rest.map Subtype.val))
        (rest.map (c3HiddenReply digests hidden)) =
      c3HiddenRow compress digests messages index.val (hidden index) ::
        c3HiddenRowsFor compress digests messages hidden rest
    rw [salt, ih]
    rfl

def c3ExposedTag (positions : Positions) (input : Block) : Prop :=
  ∃ i : Index, i ∈ positions ∧ c3TagField input = c3Tag i

theorem c3_opened_input_disjoint_hidden {positions : Positions} (compress : Compression) (digests : DigestTape)
    (messages : Index → Words 32) (hidden : C3HiddenTape positions) (row : Row)
    (present : row ∈ c3HiddenRows compress digests messages hidden)
    (opened : Block) (tagged : c3ExposedTag positions opened) : opened ≠ row.1 := by
  intro equal
  obtain ⟨i, selected, openedTag⟩ := tagged
  unfold c3HiddenRows c3HiddenRowsFor at present
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp present
  rw [equal] at openedTag
  change c3TagField (c3HiddenInput compress j.val (messages j.val) (hidden j).1) = c3Tag i at openedTag
  rw [c3_hidden_tag] at openedTag
  exact j.property (c3_tag_injective openedTag ▸ selected)

theorem c3_planned_input_hits_reference {positions : Positions} (compress : Compression) (digests : DigestTape)
    (messages : Index → Words 32) (hidden : C3HiddenTape positions) (firstStage opened : List Row)
    (tags : ∀ row ∈ opened, c3ExposedTag positions row.1) :
    let indices := hiddenIndices positions
    let plans := c3LeafPlans compress messages (c3HiddenSalts hidden) (indices.map Subtype.val)
    let tape := indices.map (c3HiddenReply digests hidden)
    plannedInputHit (opened ++ firstStage) [] plans tape →
      ∃ old ∈ firstStage, c3HitsHidden compress digests messages old hidden := by
  classical
  dsimp only
  unfold plannedInputHit
  rw [c3_hidden_rows_match_plans]
  rintro ⟨row, present, hit⟩
  change row ∈ c3HiddenRows compress digests messages hidden at present
  have found : ∃ old ∈ opened ++ firstStage, old.1 = row.1 := by
    simpa [UnusedInput] using hit
  obtain ⟨old, oldIn, note⟩ := found
  rcases List.mem_append.mp oldIn with exposed | original
  · exact False.elim (c3_opened_input_disjoint_hidden compress digests messages hidden row present old.1
      (tags old exposed) note)
  · refine ⟨old, original, ?_⟩
    unfold c3HiddenRows c3HiddenRowsFor at present
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp present
    exact Or.inl ⟨i, note.symm⟩

theorem c3_ideal_first_stage_hit_le {positions : Positions} (compress : Compression) (digests : DigestTape)
    (messages : Index → Words 32) (firstStage opened : List Row)
    (tags : ∀ row ∈ opened, c3ExposedTag positions row.1) :
    Pr{let hidden ← sampleC3HiddenTape positions}[
      let indices := hiddenIndices positions
      let plans := c3LeafPlans compress messages (c3HiddenSalts hidden) (indices.map Subtype.val)
      let tape := indices.map (c3HiddenReply digests hidden)
      plannedInputHit (opened ++ firstStage) [] plans tape] ≤
      (firstStage.length : ENNReal) * c3HiddenRate := by
  apply le_trans _ (c3_fixed_reference_trace_hit_le positions compress digests messages firstStage)
  apply prEvent_mono
  intro hidden hit
  exact c3_planned_input_hits_reference compress digests messages hidden firstStage opened tags hit

/-! ### Honest proposals -/

theorem c3_independent_honest_proposals {α : Type} (positions : Positions) (opened : OpenedDigests positions)
    (next : (Index → BitVec 128) → List Block → ProbComp α) :
    (do let salts ← $ᵗ UnopenedSalts positions
        let tape ← sampleProposalTape (hiddenIndices positions).length
        next (publicSaltTape salts) tape) =ᵈ
      (do let digests ← $ᵗ UnopenedDigestTape positions
          let hidden ← sampleC3HiddenTape positions
          next (c3HiddenSalts hidden)
            ((hiddenIndices positions).map (c3HiddenReply (fullDigestTape opened digests) hidden))) := by
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
    trans (do let raw ← $ᵗ C3RawTape positions
              paired (combine raw).1 (combine raw).2)
    · have same := uniform_transport_bind (transportOfEquiv combine.symm)
        (fun pair => paired pair.1 pair.2)
      rw [SampleableType.uniformSample_prod_eq_bind] at same
      simp only [bind_assoc, pure_bind] at same
      exact same
    · let fromSecret (digests : UnopenedDigestTape positions) (hidden : C3HiddenTape positions) :=
        next (c3HiddenSalts hidden) (indices.map (c3HiddenReply (fullDigestTape opened digests) hidden))
      trans (do let raw ← $ᵗ C3RawTape positions
                let pieces := c3FactorReplies positions raw
                fromSecret pieces.1 pieces.2)
      · apply EvalDistEq.bind_right
        intro raw
        dsimp only [paired, fromSecret]
        have sameSalts : publicSaltTape (combine raw).1 = c3HiddenSalts (c3FactorReplies positions raw).2 := by
          funext i
          unfold publicSaltTape c3HiddenSalts
          split <;> rfl
        have sameReplies : (combine raw).2 =
            c3HiddenReply (fullDigestTape opened (c3FactorReplies positions raw).1)
              (c3FactorReplies positions raw).2 := by
          funext i
          have closed := i.property
          simp only [c3HiddenReply, fullDigestTape, closed, dite_false]
          change (raw i).2 = (raw i).2.extractLsb' 256 1344 ++ (raw i).2.extractLsb' 0 256
          have joined : (raw i).2.extractLsb' 256 1344 ++ (raw i).2.extractLsb' 0 256 = (raw i).2 :=
            BitVec.extractLsb'_append_extractLsb'
          exact joined.symm
        rw [sameSalts, sameReplies]
      · exact c3_expose_unopened_digests positions fromSecret

noncomputable def c3UnopenedPlans (positions : Positions) (compress : Compression)
    (messages : Index → Words 32) (salts : Index → BitVec 128) : List InputPlan :=
  c3LeafPlans compress messages salts ((hiddenIndices positions).map Subtype.val)

theorem c3_honest_proposal_conflict_le {positions : Positions} (cache : Cache) (compress : Compression)
    (messages : Index → Words 32)
    (openedDigests : OpenedDigests positions) (firstStage openedRows : List Row) (budget : Nat)
    (seed : cache.entries = openedRows ++ firstStage) (firstCount : firstStage.length ≤ budget)
    (openedCount : openedRows.length ≤ positions.card)
    (tags : ∀ row ∈ openedRows, c3ExposedTag positions row.1) :
    Pr{let flag ← (($ᵗ UnopenedSalts positions) >>= fun salts =>
      proposedConflict cache [] (c3UnopenedPlans positions compress messages (publicSaltTape salts)))}[
      flag = true] ≤
      (budget : ENNReal) * c3HiddenRate + (2 ^ 24 : ENNReal) * (((budget : ENNReal) + 2 ^ 24) / 2 ^ 1600) := by
  classical
  let indices := hiddenIndices positions
  let count := indices.length
  let plan (salts : Index → BitVec 128) := c3UnopenedPlans positions compress messages salts
  let input (salts : Index → BitVec 128) := plannedInputHit cache.entries [] (plan salts)
  let outputAllowance := (2 ^ 24 : ENNReal) * (((budget : ENNReal) + 2 ^ 24) / 2 ^ 1600)
  have lengthOf (salts : Index → BitVec 128) : (plan salts).length = count := by
    simp [plan, count, indices, c3UnopenedPlans, c3_leaf_plans_length]
  have total := hidden_index_count positions
  have plansBound : count ≤ 2 ^ 24 := by dsimp [count, indices]; omega
  have withReplies : cache.entries.length + count ≤ budget + 2 ^ 24 := by
    rw [seed, List.length_append]
    dsimp [count, indices]
    omega
  have outputBound (salts : Index → BitVec 128) :
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
  have nodup : (indices.map (Subtype.val : HiddenIndex positions → Index)).Nodup :=
    (Finset.nodup_toList _).map Subtype.val_injective
  have bound (salts : UnopenedSalts positions) :
      Pr{let flag ← proposedConflict cache [] (plan (publicSaltTape salts))}[flag = true] ≤
        outputAllowance + Pr{let tape ← sampleProposalTape count}[input (publicSaltTape salts) tape] := by
    have proposed := proposal_conflict_decompose cache [] (plan (publicSaltTape salts))
      (fun tape possible => c3_leaf_plan_inputs_distinct compress messages _ _ nodup [] tape possible)
    refine proposed.trans ((add_le_add ?_ (outputBound _)).trans_eq (add_comm _ _))
    rw [lengthOf]
  rw [prEvent_bind_eq_tsum]
  refine (tsum_prEvent_mul_le_add_of_le ($ᵗ UnopenedSalts positions) bound).trans ?_
  have inputDist :=
    (c3_independent_honest_proposals positions openedDigests (fun salts tape => pure (input salts tape))).prEvent_eq id
  have prefixEvent :
      (∑' salts, Pr{let y ← $ᵗ UnopenedSalts positions}[y = salts] *
        Pr{let tape ← sampleProposalTape count}[input (publicSaltTape salts) tape]) ≤
          (budget : ENNReal) * c3HiddenRate := by
    have translated : (∑' salts, Pr{let y ← $ᵗ UnopenedSalts positions}[y = salts] *
        Pr{let tape ← sampleProposalTape count}[input (publicSaltTape salts) tape]) =
        Pr{let event ← (do let salts ← $ᵗ UnopenedSalts positions
                            let tape ← sampleProposalTape count
                            pure (input (publicSaltTape salts) tape))}[id event] := by
      rw [prEvent_bind_eq_tsum]
      simp only [bind_pure_comp, prEvent_map, id_eq]
    rw [translated, inputDist]
    apply prEvent_bind_le_of_forall_le_of_support
    intro closed _
    have each := c3_ideal_first_stage_hit_le compress (fullDigestTape openedDigests closed) messages
      firstStage openedRows tags
    have castFirst : (firstStage.length : ENNReal) ≤ (budget : ENNReal) := by exact_mod_cast firstCount
    have cost := each.trans (mul_le_mul_of_nonneg_right castFirst zero_le)
    simp only [bind_pure_comp, prEvent_map, id_eq]
    simpa [input, plan, c3UnopenedPlans, seed, indices] using cost
  exact (add_le_add le_rfl prefixEvent).trans_eq (add_comm _ _)

end TwoPermutationPrototype.Sampling
