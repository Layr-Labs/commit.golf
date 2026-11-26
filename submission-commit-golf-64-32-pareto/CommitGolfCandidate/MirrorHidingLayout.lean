import CommitGolfCandidate.TwoPermutationHidingIndependent
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fin.Tuple.Basic

/-! # Hiding for a mirrored one-call leaf: the layout and the hidden rows

A mirrored leaf hashes its entry with one permutation call whose input has one of two layouts,
chosen by the position (`side`). Each layout has its own tag window, its own salt window and its
own digest window. `MirrorLayout` lists what the hiding proof uses:

* the tag window of a leaf's own layout holds the tag of its position, and tags tell positions of
  one side apart (`tag_input`, `tag_injective`);
* the salt window of a leaf's own layout holds its salt (`salt_input`);
* the salt window of the other layout does not depend on the leaf's salt (`salt_foreign`): there
  the input holds message bytes or compression replies;
* a reply splits into the 256 digest bits and 1344 private bits, by position (`split`).

Against the single-layout leaf two facts are lost. A query can carry the tag of one leaf of each
side, so it can hit two hidden inputs: the rate of one query is `2/2^128 + 2^24/2^1344`
(`fixed_reference_hit_le`). And the honest inputs of two leaves of different sides can be equal.
By `cross_salt` that forces each of the two salts to one value fixed by the other leaf's entry,
which is what MirrorHidingCoincide.lean charges. Leaves of one side still have different inputs
(`same_side_ne`).

This module is the counterpart of `C3HidingCore`. It imports the leader's modules only. -/
namespace TwoPermutationPrototype.Sampling.Mirror
open CommitGolf OracleComp MeasureTheory CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option exponentiation.threshold 2048
set_option autoImplicit false

noncomputable local instance mirrorFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

/-- The part of a mirrored one-call leaf that the hiding proof uses. -/
structure MirrorLayout where
  /-- The permutation input of the leaf at a position, for an entry and a salt. -/
  input : Compression → Index → Words 32 → BitVec 128 → Block
  /-- Which of the two layouts a position uses. -/
  side : Index → Bool
  /-- The tag window of each layout. -/
  tagField : Bool → Block → BitVec 64
  /-- The tag of a position. -/
  tag : Index → BitVec 64
  /-- The salt window of each layout. -/
  saltField : Bool → Block → BitVec 128
  /-- A reply as its digest and its 1344 private bits. -/
  split : Index → (Block ≃ BitVec 256 × BitVec 1344)
  tag_injective : ∀ i j : Index, side i = side j → tag i = tag j → i = j
  tag_input : ∀ compress i message salt, tagField (side i) (input compress i message salt) = tag i
  salt_input : ∀ compress i message salt, saltField (side i) (input compress i message salt) = salt
  salt_foreign : ∀ compress i message salt salt',
    saltField (!side i) (input compress i message salt) =
      saltField (!side i) (input compress i message salt')

namespace MirrorLayout
variable (Λ : MirrorLayout)

/-- The digest of a reply at a position. -/
def digest (i : Index) (reply : Block) : BitVec 256 := (Λ.split i reply).1

/-- The reply with a given digest and private part. -/
def reply (i : Index) (digest : BitVec 256) (tail : BitVec 1344) : Block := (Λ.split i).symm (digest, tail)

theorem digest_reply (i : Index) (digest : BitVec 256) (tail : BitVec 1344) :
    Λ.digest i (Λ.reply i digest tail) = digest := by
  simp [MirrorLayout.digest, MirrorLayout.reply]

theorem reply_injective (i : Index) (digest : BitVec 256) : Function.Injective (Λ.reply i digest) := by
  intro left right same
  have pair := (Λ.split i).symm.injective same
  exact (Prod.mk.inj pair).2

theorem input_injective (compress : Compression) (i : Index) (message : Words 32) :
    Function.Injective (Λ.input compress i message) := by
  intro left right same
  have field := congrArg (Λ.saltField (Λ.side i)) same
  rwa [Λ.salt_input, Λ.salt_input] at field

/-- Two leaves of one side never share an input. -/
theorem same_side_ne {compress : Compression} {i j : Index} {m m' : Words 32} {s s' : BitVec 128}
    (sides : Λ.side i = Λ.side j) (different : i ≠ j) :
    Λ.input compress i m s ≠ Λ.input compress j m' s' := by
  intro same
  have field := congrArg (Λ.tagField (Λ.side i)) same
  rw [Λ.tag_input] at field
  rw [sides, Λ.tag_input] at field
  exact different (Λ.tag_injective i j sides field)

/-- The salt that a leaf of the other side needs for its input to equal an input of this leaf.
It depends on this leaf's position and entry only. -/
def foreignSalt (compress : Compression) (j : Index) (message : Words 32) : BitVec 128 :=
  Λ.saltField (!Λ.side j) (Λ.input compress j message 0)

/-- **Two leaves of different sides with one input**: the salt of each is fixed by the other
leaf's position and entry. -/
theorem cross_salt {compress : Compression} {i j : Index} {m m' : Words 32} {s s' : BitVec 128}
    (sides : Λ.side i ≠ Λ.side j) (same : Λ.input compress i m s = Λ.input compress j m' s') :
    s = Λ.foreignSalt compress j m' := by
  have flipped : Λ.side i = !Λ.side j := by
    cases left : Λ.side i <;> cases right : Λ.side j <;> simp_all
  have field := congrArg (Λ.saltField (Λ.side i)) same
  rw [Λ.salt_input] at field
  rw [flipped, Λ.salt_foreign compress j m' s' 0] at field
  exact field

end MirrorLayout

variable (Λ : MirrorLayout)

/-! ### The private tape: one salt and one reply tail per unopened leaf -/

abbrev Key := BitVec 128 × BitVec 1344
abbrev KeyTape (positions : Positions) := HiddenIndex positions → Key

noncomputable def sampleKeyTape (positions : Positions) : ProbComp (KeyTape positions) :=
  $ᵗ KeyTape positions

def hiddenRow (compress : Compression) (digests : DigestTape) (messages : Index → Words 32)
    (i : Index) (key : Key) : Row :=
  (Λ.input compress i (messages i) key.1, Λ.reply i (digests i) key.2)

def HitsHidden {positions : Positions} (compress : Compression) (digests : DigestTape)
    (messages : Index → Words 32) (query : Row) (hidden : KeyTape positions) : Prop :=
  (∃ i : HiddenIndex positions, (hiddenRow Λ compress digests messages i (hidden i)).1 = query.1) ∨
  (∃ i : HiddenIndex positions, (hiddenRow Λ compress digests messages i (hidden i)).2 = query.2)

theorem uniform_injective_guess {β : Type} {width : Nat} (f : BitVec width → β)
    (unique : Function.Injective f) (guess : β) :
    Pr{let hidden ← $ᵗ BitVec width}[f hidden = guess] ≤ (1 : ENNReal) / 2 ^ width := by
  let : MeasurableSpace (BitVec width) := ⊤
  let event : Set (BitVec width) := {value | f value = guess}
  have size : event.encard ≤ (1 : ℕ∞) := by
    by_cases existsHit : ∃ value, f value = guess
    · obtain ⟨hit, found⟩ := existsHit
      apply (Set.encard_mono (b := {hit}) ?_).trans (by simp)
      intro value equal
      exact Set.mem_singleton_iff.mpr (unique (equal.trans found.symm))
    · have empty : event = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro value equal
        exact existsHit ⟨value, equal⟩
      simp [empty]
  have chance := SampleableType.evalDist_uniformSample_le_of_encard_le event 1 size
  rw [prEvent_eq_evalDist_of_discrete]
  simpa only [Nat.cast_one, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat] using chance

theorem coordinate_probability {positions : Positions} (index : HiddenIndex positions)
    (event : Key → Prop) :
    Pr{let hidden ← sampleKeyTape positions}[event (hidden index)] =
      Pr{let key ← $ᵗ Key}[event key] := by
  have sampled := uniform_tape_coordinate (ι := HiddenIndex positions) (α := Key)
    (β := Key) index (fun key => pure key)
  have eventEqual := sampled.prEvent_eq event
  rw [bind_pure_comp, prEvent_map, bind_pure] at eventEqual
  exact eventEqual

theorem tagged_event_le {ι α : Type} (sample : ProbComp α)
    (event : ι → α → Prop) {tag : ι → Prop} (unique : ∀ i j, tag i → tag j → i = j)
    (impliesTag : ∀ i key, event i key → tag i) (rate : ENNReal)
    (bound : ∀ i, Pr{let key ← sample}[event i key] ≤ rate) :
    Pr{let key ← sample}[∃ i, event i key] ≤ rate := by
  classical
  by_cases hasTag : ∃ i, tag i
  · obtain ⟨selected, fitted⟩ := hasTag
    refine (prEvent_mono _ (p := fun key => ∃ i, event i key)
      (q := event selected) ?_).trans (bound selected)
    rintro key ⟨i, hit⟩
    rwa [← unique i selected (impliesTag i key hit) fitted]
  · have zero : Pr{let key ← sample}[∃ i, event i key] = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ (fun key _ hit => by
        obtain ⟨i, hit⟩ := hit
        exact hasTag ⟨i, impliesTag i key hit⟩)
    rw [zero]
    exact zero_le

theorem drop_independent_suffix {α β : Type} (left : ProbComp α) (right : ProbComp β) :
    (do let value ← left; let _ ← right; pure value) =ᵈ left := by
  trans (left >>= pure)
  · apply EvalDistEq.bind_right
    intro value
    let : MeasurableSpace α := ⊤
    exact EvalDistEq.of_evalDist_eq (evalDist_bind_const right (pure value))
  · rw [bind_pure]

theorem key_input {positions : Positions} (compress : Compression) (i : HiddenIndex positions)
    (digests : DigestTape) (messages : Index → Words 32) (guess : Block) :
    Pr{let hidden ← sampleKeyTape positions}[
      (hiddenRow Λ compress digests messages i (hidden i)).1 = guess] ≤ (1 : ENNReal) / 2 ^ 128 := by
  rw [coordinate_probability i (fun key => (hiddenRow Λ compress digests messages i key).1 = guess)]
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [hiddenRow]
  apply le_trans _ (uniform_injective_guess _ (Λ.input_injective compress i (messages i)) guess)
  have equal := (drop_independent_suffix ($ᵗ BitVec 128) ($ᵗ BitVec 1344)).prEvent_eq
    (fun salt => Λ.input compress i (messages i) salt = guess)
  exact equal.le

theorem key_output {positions : Positions} (compress : Compression) (i : HiddenIndex positions)
    (digests : DigestTape) (messages : Index → Words 32) (guess : Block) :
    Pr{let hidden ← sampleKeyTape positions}[
      (hiddenRow Λ compress digests messages i (hidden i)).2 = guess] ≤ (1 : ENNReal) / 2 ^ 1344 := by
  rw [coordinate_probability i (fun key => (hiddenRow Λ compress digests messages i key).2 = guess)]
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [hiddenRow]
  apply prEvent_bind_le_of_forall_le_of_support
  intro salt _
  change Pr{let _ ← _}[_] ≤ _
  rw [bind_pure_comp, prEvent_map]
  exact uniform_injective_guess _ (Λ.reply_injective i (digests i)) guess

/-- The detection rate of one query against all hidden rows. The input can carry the tag of one
leaf of each side and a 128-bit salt; the output must match 1344 private bits of one of at most
`2^24` replies. -/
noncomputable def hiddenRate : ENNReal :=
  (1 / 2 ^ 128 + 1 / 2 ^ 128) + (2 ^ 24 : ENNReal) * (1 / 2 ^ 1344)

/-- **One query against the hidden rows.** Replaces `c3_fixed_reference_hit_le`: the query can
name two leaves, one of each side. -/
theorem fixed_reference_hit_le (positions : Positions) (compress : Compression) (digests : DigestTape)
    (messages : Index → Words 32) (query : Row) :
    Pr{let hidden ← sampleKeyTape positions}[
      HitsHidden Λ compress digests messages query hidden] ≤ hiddenRate := by
  classical
  let sample := sampleKeyTape positions
  let inputSide (b : Bool) (i : HiddenIndex positions) (hidden : KeyTape positions) : Prop :=
    Λ.side i.val = b ∧ (hiddenRow Λ compress digests messages i (hidden i)).1 = query.1
  let output (i : HiddenIndex positions) (hidden : KeyTape positions) :=
    (hiddenRow Λ compress digests messages i (hidden i)).2 = query.2
  have sideBound (b : Bool) : Pr{let hidden ← sample}[∃ i, inputSide b i hidden] ≤ (1 : ENNReal) / 2 ^ 128 := by
    apply tagged_event_le (tag := fun i : HiddenIndex positions =>
      Λ.side i.val = b ∧ Λ.tag i.val = Λ.tagField b query.1)
    · rintro i j ⟨sideI, tagI⟩ ⟨sideJ, tagJ⟩
      exact Subtype.ext (Λ.tag_injective i.val j.val (sideI.trans sideJ.symm) (tagI.trans tagJ.symm))
    · rintro i hidden ⟨onSide, hit⟩
      refine ⟨onSide, ?_⟩
      have field := Λ.tag_input compress i.val (messages i.val) (hidden i).1
      change Λ.input compress i.val (messages i.val) (hidden i).1 = query.1 at hit
      rw [hit, onSide] at field
      exact field.symm
    · intro i
      exact (prEvent_mono _ _ _ (fun hidden hit => hit.2)).trans
        (key_input Λ compress i digests messages query.1)
  have number : Fintype.card (HiddenIndex positions) ≤ 2 ^ 24 := by
    have bound := Fintype.card_le_of_injective (fun i : HiddenIndex positions => i.val) Subtype.val_injective
    have indexSize : Fintype.card Index = 2 ^ 24 := Fintype.card_fin _
    exact bound.trans_eq indexSize
  have castNumber : (Fintype.card (HiddenIndex positions) : ENNReal) ≤ 2 ^ 24 := by
    have casted : (Fintype.card (HiddenIndex positions) : ENNReal) ≤ ((2 ^ 24 : Nat) : ENNReal) :=
      Nat.cast_le.mpr number
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using casted
  have zBound : Pr{let hidden ← sample}[∃ i, output i hidden] ≤ (2 ^ 24 : ENNReal) * (1 / 2 ^ 1344) := by
    calc
      _ = Pr{let hidden ← sample}[∃ i ∈ (Finset.univ : Finset (HiddenIndex positions)), output i hidden] := by simp
      _ ≤ ∑ i : HiddenIndex positions, Pr{let hidden ← sample}[output i hidden] :=
        prEvent_exists_finset_le _ _ _
      _ ≤ ∑ _i : HiddenIndex positions, (1 : ENNReal) / 2 ^ 1344 :=
        Finset.sum_le_sum (fun i _ => key_output Λ compress i digests messages query.2)
      _ = (Fintype.card (HiddenIndex positions) : ENNReal) * (1 / 2 ^ 1344) := by simp [nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right castNumber zero_le
  have aBound : Pr{let hidden ← sample}[
      (∃ i, inputSide false i hidden) ∨ (∃ i, inputSide true i hidden)] ≤
      (1 : ENNReal) / 2 ^ 128 + 1 / 2 ^ 128 :=
    (prEvent_or_le sample _ _).trans (add_le_add (sideBound false) (sideBound true))
  refine (prEvent_mono sample _ (fun hidden =>
    ((∃ i, inputSide false i hidden) ∨ (∃ i, inputSide true i hidden)) ∨ ∃ i, output i hidden) ?_).trans
    ((prEvent_or_le sample _ _).trans (add_le_add aBound zBound))
  rintro hidden (⟨i, hit⟩ | found)
  · cases onSide : Λ.side i.val
    · exact Or.inl (Or.inl ⟨i, onSide, hit⟩)
    · exact Or.inl (Or.inr ⟨i, onSide, hit⟩)
  · exact Or.inr found

theorem fixed_reference_trace_hit_le (positions : Positions) (compress : Compression)
    (digests : DigestTape) (messages : Index → Words 32) (trace : List Row) :
    Pr{let hidden ← sampleKeyTape positions}[
      ∃ row ∈ trace, HitsHidden Λ compress digests messages row hidden] ≤
      (trace.length : ENNReal) * hiddenRate :=
  prEvent_list_le trace (sampleKeyTape positions)
    (fun row hidden => HitsHidden Λ compress digests messages row hidden)
    hiddenRate (fun row _ => fixed_reference_hit_le Λ positions compress digests messages row)

/-! ### Plans: one forward query per leaf -/

def leafPlans (compress : Compression) (messages : Index → Words 32) (salts : Index → BitVec 128)
    (indices : List Index) : List InputPlan :=
  indices.map fun i => fun _ => Λ.input compress i (messages i) (salts i)

theorem leaf_plans_length (compress : Compression) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (indices : List Index) :
    (leafPlans Λ compress messages salts indices).length = indices.length := by
  simp [leafPlans]

/-- The inputs of the planned rows are the leaves' inputs, whatever the replies. -/
theorem leaf_plan_inputs (compress : Compression) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (indices : List Index) (answers tape : List Block)
    (length : tape.length = indices.length) :
    (plannedRows answers (leafPlans Λ compress messages salts indices) tape).map Prod.fst =
      indices.map fun i => Λ.input compress i (messages i) (salts i) := by
  induction indices generalizing answers tape with
  | nil => cases tape <;> simp [leafPlans, plannedRows]
  | cons index rest ih =>
    cases tape with
    | nil => simp at length
    | cons first tail =>
      have exactTail : tail.length = rest.length := by
        simp only [List.length_cons] at length
        omega
      change Λ.input compress index (messages index) (salts index) ::
        (plannedRows (first :: answers) (leafPlans Λ compress messages salts rest) tail).map Prod.fst =
          Λ.input compress index (messages index) (salts index) ::
            rest.map fun i => Λ.input compress i (messages i) (salts i)
      rw [ih _ _ exactTail]

/-! ### Reply tapes -/

theorem uniform_fin_block_tape {α : Type} (count : Nat) (next : List Block → ProbComp α) :
    (do let table ← $ᵗ (Fin count → Block)
        next (List.ofFn table)) =ᵈ
      (sampleProposalTape count >>= next) := by
  induction count generalizing next with
  | zero =>
    simp only [List.ofFn_zero, sampleProposalTape, pure_bind]
    let : MeasurableSpace α := ⊤
    exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const _ _)
  | succ count ih =>
    let vec := Fin.consEquiv (fun _ : Fin (count + 1) => Block)
    apply (uniform_transport_bind (transportOfEquiv vec.symm)
      (fun table => next (List.ofFn table))).trans
    rw [SampleableType.uniformSample_prod_eq_bind]
    rw [sampleProposalTape]
    simp only [bind_assoc, pure_bind]
    apply EvalDistEq.bind_right
    intro first
    change (do let table ← $ᵗ (Fin count → Block)
               next (List.ofFn (Fin.cons first table))) =ᵈ _
    simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    apply (ih (fun tape => next (first :: tape))).trans
    rfl

theorem uniform_enum_block_tape {ι α : Type} [Fintype ι] (indices : List ι) (distinct : indices.Nodup)
    (covers : ∀ i : ι, i ∈ indices) (next : List Block → ProbComp α) :
    (do let table ← $ᵗ (ι → Block)
        next (indices.map table)) =ᵈ
      (sampleProposalTape indices.length >>= next) := by
  classical
  let numbering := List.Nodup.getEquivOfForallMemList indices distinct covers
  let tableEquiv : (ι → Block) ≃ (Fin indices.length → Block) :=
    Equiv.arrowCongr numbering.symm (Equiv.refl _)
  apply (uniform_transport_bind (transportOfEquiv tableEquiv)
    (fun table => next (indices.map table))).trans
  apply (EvalDistEq.bind_right _ (fun table => ?_)).trans (uniform_fin_block_tape indices.length next)
  have same : indices.map (tableEquiv.symm table) = List.ofFn table := by
    calc
      _ = (List.ofFn indices.get).map (tableEquiv.symm table) :=
        congrArg (List.map (tableEquiv.symm table)) (List.ofFn_get indices).symm
      _ = _ := by
        rw [List.map_ofFn]
        congr 1
        funext i
        change table (numbering.symm (indices.get i)) = table i
        exact congrArg table (numbering.symm_apply_apply i)
  change next (indices.map (tableEquiv.symm table)) =ᵈ next (List.ofFn table)
  rw [same]

abbrev RawTape (positions : Positions) := HiddenIndex positions → BitVec 128 × Block

/-- A salt and a reply as the digest and the private key. -/
def splitKey (i : Index) : (BitVec 128 × Block) ≃ (BitVec 256 × Key) where
  toFun raw := ((Λ.split i raw.2).1, raw.1, (Λ.split i raw.2).2)
  invFun separated := (separated.2.1, (Λ.split i).symm (separated.1, separated.2.2))
  left_inv raw := by
    obtain ⟨salt, reply⟩ := raw
    simp
  right_inv separated := by
    obtain ⟨digest, salt, tail⟩ := separated
    simp

def factorReplies (positions : Positions) :
    RawTape positions ≃ (UnopenedDigestTape positions × KeyTape positions) :=
  (Equiv.piCongrRight (fun i : HiddenIndex positions => splitKey Λ i.val)).trans
    (functionPairEquiv (HiddenIndex positions) (BitVec 256) Key)

theorem expose_unopened_digests {α : Type} (positions : Positions)
    (next : UnopenedDigestTape positions → KeyTape positions → ProbComp α) :
    (do let raw ← $ᵗ RawTape positions
        let separate := factorReplies Λ positions raw
        next separate.1 separate.2) =ᵈ
      (do let digests ← $ᵗ UnopenedDigestTape positions
          let hidden ← sampleKeyTape positions
          next digests hidden) := by
  have transport := (uniform_transport_bind (transportOfEquiv (factorReplies Λ positions).symm)
    (fun pair => next pair.1 pair.2)).symm
  refine transport.trans ?_
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  rfl

end TwoPermutationPrototype.Sampling.Mirror
