import CommitGolfCandidate.MirrorHidingLayout
import CommitGolfCandidate.TwoPermutationHidingTwoStage

/-! # Hiding for a mirrored leaf: coinciding honest inputs

With one layout the tag word shows that the honest permutation inputs of different leaves differ.
With two layouts that is false across the sides: the entries can be chosen so that the input of an
even leaf equals the input of an odd leaf, for one value of each of the two salts
(`MirrorLayout.cross_salt`). The proof therefore charges an event where it had a fact.

* `tape_pair_guess`: two coordinates of a uniform salt tape take two given values with
  probability `2^-256`.
* `hidden_inputs_repeat_le`: two unopened leaves share an input with probability at most
  `2^48 / 2^256` over the unopened salts.
* `opened_hidden_coincide_le`: an opened leaf and an unopened leaf share an input with probability
  at most `2^48 / 2^256` over both salt tapes. The opened salt must take one value and the
  unopened salt another, so neither tape alone gives more than `2^-128` per pair, which would not
  be enough: an opening may hold `2^24` positions.
* `honest_proposal_conflict_le` replaces `c3_honest_proposal_conflict_le`. The honest proposals
  of the unopened leaves conflict with the cache or with each other with probability at most the
  first-stage hits, the output birthday term, `repeatAllowance`, and `openedHit`, the chance that
  an unopened input equals the input of an opened row. `openedHit` stays symbolic here and is
  averaged over the opened salts in MirrorHidingConditional.lean. -/
namespace TwoPermutationPrototype.Sampling.Mirror
open CommitGolf OracleComp MeasureTheory CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option exponentiation.threshold 2048
set_option autoImplicit false

noncomputable local instance coincideFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

local instance coincideDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

variable (Λ : MirrorLayout)

/-! ### Coordinates of a uniform salt tape -/

theorem tape_coordinate_event {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (event : BitVec 128 → Prop) :
    Pr{let tape ← $ᵗ (ι → BitVec 128)}[event (tape i)] = Pr{let value ← $ᵗ BitVec 128}[event value] := by
  have sampled := uniform_tape_coordinate (ι := ι) (α := BitVec 128) (β := BitVec 128) i
    (fun value => pure value)
  have eventEqual := sampled.prEvent_eq event
  rw [bind_pure_comp, prEvent_map, bind_pure] at eventEqual
  exact eventEqual

theorem tape_coordinate_guess {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι) (a : BitVec 128) :
    Pr{let tape ← $ᵗ (ι → BitVec 128)}[tape i = a] ≤ (1 : ENNReal) / 2 ^ 128 :=
  (tape_coordinate_event i (fun value => value = a)).le.trans
    (uniform_injective_guess id Function.injective_id a)

theorem inverse_square : (1 : ENNReal) / 2 ^ 128 * (1 / 2 ^ 128) = 1 / 2 ^ 256 := by
  simp only [one_div]
  rw [← ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by finiteness)), ← pow_add]

/-- **Two coordinates of a uniform salt tape are independent.** -/
theorem tape_pair_guess {ι : Type} [Fintype ι] [DecidableEq ι] (i j : ι) (different : i ≠ j)
    (a b : BitVec 128) :
    Pr{let tape ← $ᵗ (ι → BitVec 128)}[tape i = a ∧ tape j = b] ≤ (1 : ENNReal) / 2 ^ 256 := by
  let other : {k : ι // k ≠ i} := ⟨j, fun same => different same.symm⟩
  let read : (ι → BitVec 128) ≃ BitVec 128 × ({k : ι // k ≠ i} → BitVec 128) :=
    Equiv.piSplitAt i (fun _ => BitVec 128)
  let event : BitVec 128 × ({k : ι // k ≠ i} → BitVec 128) → Prop :=
    fun pair => pair.1 = a ∧ pair.2 other = b
  have separated := (uniform_transport_bind (transportOfEquiv read.symm)
    (fun pair => (pure pair : ProbComp (BitVec 128 × ({k : ι // k ≠ i} → BitVec 128))))).symm
  have eventEqual := separated.prEvent_eq event
  rw [bind_pure_comp, prEvent_map, bind_pure] at eventEqual
  refine (le_of_eq ?_).trans (?_ : Pr{let pair ← $ᵗ (BitVec 128 × ({k : ι // k ≠ i} → BitVec 128))}[
    event pair] ≤ _)
  · exact eventEqual
  · rw [SampleableType.uniformSample_prod_eq_bind]
    have inner (first : BitVec 128) :
        Pr{let pair ← (do let rest ← $ᵗ ({k : ι // k ≠ i} → BitVec 128)
                          pure (first, rest))}[event pair] ≤
          (if first = a then (1 : ENNReal) / 2 ^ 128 else 0) := by
      rw [bind_pure_comp, prEvent_map]
      by_cases hit : first = a
      · rw [if_pos hit]
        exact (prEvent_mono _ _ _ (fun rest found => found.2)).trans (tape_coordinate_guess other b)
      · rw [if_neg hit]
        exact (prEvent_eq_zero_of_forall_mem_support _ _ (fun rest _ found => hit found.1)).le
    refine (prEvent_bind_le_prEvent_mul_of_forall_le_of_support ($ᵗ BitVec 128) _
      (fun first => first = a) event (ε := (1 : ENNReal) / 2 ^ 128) ?_ ?_).trans ?_
    · intro first _ hit
      exact (inner first).trans_eq (if_pos hit)
    · intro first _ miss
      exact le_antisymm ((inner first).trans_eq (if_neg miss)) zero_le
    · exact (mul_le_mul_of_nonneg_right (uniform_injective_guess id Function.injective_id a) zero_le).trans_eq
        inverse_square

/-! ### One block against the unopened inputs -/

/-- One block equals the input of some unopened leaf with probability at most `2/2^128`: it can
carry the tag of one leaf of each side. -/
theorem salts_input_guess_le (positions : Positions) (compress : Compression)
    (messages : Index → Words 32) (guess : Block) :
    Pr{let salts ← $ᵗ UnopenedSalts positions}[
      ∃ j : HiddenIndex positions, Λ.input compress j.val (messages j.val) (salts j) = guess] ≤
      (1 : ENNReal) / 2 ^ 128 + 1 / 2 ^ 128 := by
  classical
  let sample : ProbComp (UnopenedSalts positions) := $ᵗ UnopenedSalts positions
  let onSide (b : Bool) (j : HiddenIndex positions) (salts : UnopenedSalts positions) : Prop :=
    Λ.side j.val = b ∧ Λ.input compress j.val (messages j.val) (salts j) = guess
  have each (j : HiddenIndex positions) :
      Pr{let salts ← sample}[Λ.input compress j.val (messages j.val) (salts j) = guess] ≤
        (1 : ENNReal) / 2 ^ 128 :=
    (tape_coordinate_event j
      (fun salt => Λ.input compress j.val (messages j.val) salt = guess)).le.trans
      (uniform_injective_guess _ (Λ.input_injective compress j.val (messages j.val)) guess)
  have sideBound (b : Bool) : Pr{let salts ← sample}[∃ j, onSide b j salts] ≤ (1 : ENNReal) / 2 ^ 128 := by
    apply tagged_event_le (tag := fun j : HiddenIndex positions =>
      Λ.side j.val = b ∧ Λ.tag j.val = Λ.tagField b guess)
    · rintro i j ⟨sideI, tagI⟩ ⟨sideJ, tagJ⟩
      exact Subtype.ext (Λ.tag_injective i.val j.val (sideI.trans sideJ.symm) (tagI.trans tagJ.symm))
    · rintro j salts ⟨found, hit⟩
      refine ⟨found, ?_⟩
      have field := Λ.tag_input compress j.val (messages j.val) (salts j)
      rw [hit, found] at field
      exact field.symm
    · intro j
      exact (prEvent_mono _ _ _ (fun salts hit => hit.2)).trans (each j)
  refine (prEvent_mono sample _ (fun salts =>
    (∃ j, onSide false j salts) ∨ (∃ j, onSide true j salts)) ?_).trans
    ((prEvent_or_le sample _ _).trans (add_le_add (sideBound false) (sideBound true)))
  rintro salts ⟨j, hit⟩
  cases found : Λ.side j.val
  · exact Or.inl ⟨j, found, hit⟩
  · exact Or.inr ⟨j, found, hit⟩

/-! ### Two unopened leaves with one input -/

/-- The inputs of the unopened leaves, in the order of `hiddenIndices`. -/
noncomputable def hiddenInputs (positions : Positions) (compress : Compression)
    (messages : Index → Words 32) (salts : UnopenedSalts positions) : List Block :=
  (hiddenIndices positions).map fun j => Λ.input compress j.val (messages j.val) (salts j)

/-- The allowance for two honest inputs that coincide: `2^48` pairs at `2^-256`. -/
noncomputable def repeatAllowance : ENNReal := (2 ^ 24 * 2 ^ 24 : ENNReal) * (1 / 2 ^ 256)

theorem hidden_card_le (positions : Positions) :
    (Fintype.card (HiddenIndex positions) : ENNReal) ≤ 2 ^ 24 := by
  have bound := Fintype.card_le_of_injective (fun i : HiddenIndex positions => i.val) Subtype.val_injective
  have indexSize : Fintype.card Index = 2 ^ 24 := Fintype.card_fin _
  have casted : (Fintype.card (HiddenIndex positions) : ENNReal) ≤ ((2 ^ 24 : Nat) : ENNReal) :=
    Nat.cast_le.mpr (bound.trans_eq indexSize)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using casted

theorem opened_card_le (positions : Positions) :
    (Fintype.card {i : Index // i ∈ positions} : ENNReal) ≤ 2 ^ 24 := by
  have bound := Fintype.card_le_of_injective (fun i : {i : Index // i ∈ positions} => i.val)
    Subtype.val_injective
  have indexSize : Fintype.card Index = 2 ^ 24 := Fintype.card_fin _
  have casted : (Fintype.card {i : Index // i ∈ positions} : ENNReal) ≤ ((2 ^ 24 : Nat) : ENNReal) :=
    Nat.cast_le.mpr (bound.trans_eq indexSize)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using casted

/-- **Two unopened leaves share an input** with probability at most `repeatAllowance`. Replaces
the deterministic `c3_leaf_plan_inputs_distinct`. -/
theorem hidden_inputs_repeat_le (positions : Positions) (compress : Compression)
    (messages : Index → Words 32) :
    Pr{let salts ← $ᵗ UnopenedSalts positions}[
      ¬ (hiddenInputs Λ positions compress messages salts).Nodup] ≤ repeatAllowance := by
  classical
  let sample : ProbComp (UnopenedSalts positions) := $ᵗ UnopenedSalts positions
  let target (k : HiddenIndex positions) : BitVec 128 := Λ.foreignSalt compress k.val (messages k.val)
  let clash (pair : HiddenIndex positions × HiddenIndex positions) (salts : UnopenedSalts positions) : Prop :=
    pair.1 ≠ pair.2 ∧ salts pair.1 = target pair.2 ∧ salts pair.2 = target pair.1
  have each (pair : HiddenIndex positions × HiddenIndex positions) :
      Pr{let salts ← sample}[clash pair salts] ≤ (1 : ENNReal) / 2 ^ 256 := by
    by_cases different : pair.1 = pair.2
    · exact (prEvent_eq_zero_of_forall_mem_support _ _ (fun salts _ found => found.1 different)).le.trans
        zero_le
    · exact (prEvent_mono _ _ _ (fun salts found => found.2)).trans
        (tape_pair_guess pair.1 pair.2 different _ _)
  have union := prEvent_exists_le_card_mul sample clash each
  have count : (Fintype.card (HiddenIndex positions × HiddenIndex positions) : ENNReal) ≤ 2 ^ 24 * 2 ^ 24 := by
    rw [Fintype.card_prod, Nat.cast_mul]
    exact mul_le_mul' (hidden_card_le positions) (hidden_card_le positions)
  refine (prEvent_mono sample _ (fun salts => ∃ pair, clash pair salts) ?_).trans
    (union.trans (mul_le_mul_of_nonneg_right count zero_le))
  intro salts repeated
  by_contra none
  apply repeated
  unfold hiddenInputs hiddenIndices
  refine (Finset.nodup_toList _).map_on ?_
  intro i _ j _ same
  by_contra different
  by_cases sides : Λ.side i.val = Λ.side j.val
  · exact Λ.same_side_ne sides (fun equal => different (Subtype.ext equal)) same
  · exact none ⟨(i, j), different, Λ.cross_salt sides same, Λ.cross_salt (Ne.symm sides) same.symm⟩

/-! ### An opened leaf and an unopened leaf with one input -/

/-- **An opened and an unopened leaf share an input** with probability at most `repeatAllowance`
over both salt tapes. Replaces the deterministic `c3_opened_input_disjoint_hidden`. The opened
leaves use `opened`, the entries they have in both worlds. -/
theorem opened_hidden_coincide_le (positions : Positions) (compress : Compression)
    (opened messages : Index → Words 32) :
    Pr{let pair ← (do let shown ← $ᵗ OpenedSalts positions
                      let closed ← $ᵗ UnopenedSalts positions
                      pure (shown, closed))}[
      ∃ (i : {i : Index // i ∈ positions}) (j : HiddenIndex positions),
        Λ.input compress i.val (opened i.val) (pair.1 i) =
          Λ.input compress j.val (messages j.val) (pair.2 j)] ≤ repeatAllowance := by
  classical
  let sample : ProbComp (OpenedSalts positions × UnopenedSalts positions) := do
    let shown ← $ᵗ OpenedSalts positions
    let closed ← $ᵗ UnopenedSalts positions
    pure (shown, closed)
  let clash (pair : {i : Index // i ∈ positions} × HiddenIndex positions)
      (salts : OpenedSalts positions × UnopenedSalts positions) : Prop :=
    salts.1 pair.1 = Λ.foreignSalt compress pair.2.val (messages pair.2.val) ∧
      salts.2 pair.2 = Λ.foreignSalt compress pair.1.val (opened pair.1.val)
  have each (pair : {i : Index // i ∈ positions} × HiddenIndex positions) :
      Pr{let salts ← sample}[clash pair salts] ≤ (1 : ENNReal) / 2 ^ 256 := by
    refine (prEvent_bind_le_prEvent_mul_of_forall_le_of_support ($ᵗ OpenedSalts positions) _
      (fun shown => shown pair.1 = Λ.foreignSalt compress pair.2.val (messages pair.2.val))
      (clash pair) (ε := (1 : ENNReal) / 2 ^ 128) ?_ ?_).trans ?_
    · intro shown _ _
      rw [bind_pure_comp, prEvent_map]
      exact (prEvent_mono _ _ _ (fun closed found => found.2)).trans (tape_coordinate_guess pair.2 _)
    · intro shown _ miss
      rw [bind_pure_comp, prEvent_map]
      exact prEvent_eq_zero_of_forall_mem_support _ _ (fun closed _ found => miss found.1)
    · exact (mul_le_mul_of_nonneg_right (tape_coordinate_guess pair.1 _) zero_le).trans_eq inverse_square
  have union := prEvent_exists_le_card_mul sample clash each
  have count : (Fintype.card ({i : Index // i ∈ positions} × HiddenIndex positions) : ENNReal) ≤
      2 ^ 24 * 2 ^ 24 := by
    rw [Fintype.card_prod, Nat.cast_mul]
    exact mul_le_mul' (opened_card_le positions) (hidden_card_le positions)
  refine (prEvent_mono sample _ (fun salts => ∃ pair, clash pair salts) ?_).trans
    (union.trans (mul_le_mul_of_nonneg_right count zero_le))
  rintro salts ⟨i, j, same⟩
  have different : i.val ≠ j.val := fun equal => j.property (equal ▸ i.property)
  by_cases sides : Λ.side i.val = Λ.side j.val
  · exact absurd same (Λ.same_side_ne sides different)
  · exact ⟨(i, j), Λ.cross_salt sides same, Λ.cross_salt (Ne.symm sides) same.symm⟩

end TwoPermutationPrototype.Sampling.Mirror
