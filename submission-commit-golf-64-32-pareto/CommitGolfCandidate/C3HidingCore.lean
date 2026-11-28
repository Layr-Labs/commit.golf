import CommitGolfCandidate.C3LeafModel
import CommitGolfCandidate.TwoPermutationHidingReplies
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fin.Tuple.Basic

/-! # Hiding for the 3c1p leaf: the hidden rows

For a fixed compression function, the honest permutation input of leaf `i` is
`c3HiddenInput compress i v s`: the entry words, the tag of `i`, the salt `s` and `t3`, where
`t3` is a fixed function of the entry. It is injective in the salt and its tag word names `i`.
Each unopened leaf has one hidden row: its input and its 1600-bit reply, of which the
commitment and proof only use the low 256 bits (the digest). This module is the one-row
counterpart of the leader's `TwoPermutationHidingHits`, `Tape`, `Pair`, `Plans` and `Replies`. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory CommitGolfCandidate TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
set_option exponentiation.threshold 2048
set_option autoImplicit false

noncomputable local instance c3FunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

def c3HiddenInput (compress : Compression) (index : Index) (message : Words 32) (salt : BitVec 128) : Block :=
  c3PermInput compress index (saltWords salt) message

/-- The tag word of a permutation input: bits `1152 .. 1216` (bytes `144 .. 152`). -/
def c3TagField (input : Block) : Word := input.extractLsb' (64 * 18) 64

theorem c3_tag_field_input (compress : Compression) (index : Index) (nonce : Words 2) (v : Words 32) :
    c3TagField (c3PermInput compress index nonce v) = c3Tag index := by
  have word := packed_word (c3PermWords index nonce v (digestWords (c3T3 compress v))) (⟨18, by decide⟩ : Fin 25)
  simp only [c3PermWords, show ¬ (18 < 18) by decide, dite_false, ite_true] at word
  exact word

theorem c3_tag_injective : Function.Injective c3Tag := by
  intro i j same
  have left : 4096 + 256 * i.val < 2 ^ 64 := by have := i.isLt; change i.val < 2^24 at this; omega
  have right : 4096 + 256 * j.val < 2 ^ 64 := by have := j.isLt; change j.val < 2^24 at this; omega
  have raw := congrArg BitVec.toNat same
  simp only [c3Tag, BitVec.toNat_ofNat, Nat.mod_eq_of_lt left, Nat.mod_eq_of_lt right] at raw
  exact Fin.ext (by omega)

theorem c3_hidden_tag (compress : Compression) (index : Index) (message : Words 32) (salt : BitVec 128) :
    c3TagField (c3HiddenInput compress index message salt) = c3Tag index :=
  c3_tag_field_input compress index (saltWords salt) message

theorem c3_salt_words_injective : Function.Injective saltWords := by
  intro left right same
  have low := congrFun same (0 : Fin 2)
  have high := congrFun same (1 : Fin 2)
  change left.extractLsb' 0 64 = right.extractLsb' 0 64 at low
  change left.extractLsb' 64 64 = right.extractLsb' 64 64 at high
  have reconstruct (value : BitVec 128) :
      value.extractLsb' 64 64 ++ value.extractLsb' 0 64 = value :=
    BitVec.extractLsb'_append_extractLsb'
  calc
    left = _ := (reconstruct left).symm
    _ = right.extractLsb' 64 64 ++ right.extractLsb' 0 64 := by rw [low, high]
    _ = right := reconstruct right

theorem c3_hidden_input_injective (compress : Compression) (index : Index) (message : Words 32) :
    Function.Injective (c3HiddenInput compress index message) := by
  intro left right same
  apply c3_salt_words_injective
  have words := packBuffer_injective same
  funext k
  have chosen := congrFun words ⟨19 + k.val, by omega⟩
  have a : ¬ (19 + k.val < 18) := by omega
  have b : ¬ (19 + k.val = 18) := by omega
  have c : 19 + k.val < 21 := by omega
  have d : 19 + k.val - 19 = k.val := by omega
  simpa [c3PermWords, a, b, c, d] using chosen

private theorem c3_uniform_injective_guess {β : Type} {width : Nat} (f : BitVec width → β)
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

theorem c3_public_guess_input_le (compress : Compression) (index : Index) (message : Words 32) (guess : Block) :
    Pr{let salt ← $ᵗ BitVec 128}[c3HiddenInput compress index message salt = guess] ≤
      (1 : ENNReal) / 2 ^ 128 :=
  c3_uniform_injective_guess _ (c3_hidden_input_injective compress index message) guess

/-! ### The private tape: one salt and one reply tail per unopened leaf -/

abbrev C3Key := BitVec 128 × BitVec 1344
abbrev C3HiddenTape (positions : Positions) := HiddenIndex positions → C3Key

noncomputable def sampleC3HiddenTape (positions : Positions) : ProbComp (C3HiddenTape positions) :=
  $ᵗ C3HiddenTape positions

def c3HiddenRow (compress : Compression) (digests : DigestTape) (messages : Index → Words 32)
    (i : Index) (key : C3Key) : Row :=
  (c3HiddenInput compress i (messages i) key.1, key.2 ++ digests i)

def c3HitsHidden {positions : Positions} (compress : Compression) (digests : DigestTape)
    (messages : Index → Words 32) (query : Row) (hidden : C3HiddenTape positions) : Prop :=
  (∃ i : HiddenIndex positions, (c3HiddenRow compress digests messages i (hidden i)).1 = query.1) ∨
  (∃ i : HiddenIndex positions, (c3HiddenRow compress digests messages i (hidden i)).2 = query.2)

private theorem c3_coordinate_probability {positions : Positions} (index : HiddenIndex positions)
    (event : C3Key → Prop) :
    Pr{let hidden ← sampleC3HiddenTape positions}[event (hidden index)] =
      Pr{let key ← $ᵗ C3Key}[event key] := by
  have sampled := uniform_tape_coordinate (ι := HiddenIndex positions) (α := C3Key)
    (β := C3Key) index (fun key => pure key)
  have eventEqual := sampled.prEvent_eq event
  rw [bind_pure_comp, prEvent_map, bind_pure] at eventEqual
  exact eventEqual

private theorem c3_tagged_event_le {ι α : Type} (sample : ProbComp α)
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

private theorem c3_drop_independent_suffix {α β : Type} (left : ProbComp α) (right : ProbComp β) :
    (do let value ← left; let _ ← right; pure value) =ᵈ left := by
  trans (left >>= pure)
  · apply EvalDistEq.bind_right
    intro value
    let : MeasurableSpace α := ⊤
    exact EvalDistEq.of_evalDist_eq (evalDist_bind_const right (pure value))
  · rw [bind_pure]

private theorem c3_key_input {positions : Positions} (compress : Compression) (i : HiddenIndex positions)
    (digests : DigestTape) (messages : Index → Words 32) (guess : Block) :
    Pr{let hidden ← sampleC3HiddenTape positions}[
      (c3HiddenRow compress digests messages i (hidden i)).1 = guess] ≤ (1 : ENNReal) / 2 ^ 128 := by
  rw [c3_coordinate_probability i (fun key => (c3HiddenRow compress digests messages i key).1 = guess)]
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [c3HiddenRow]
  apply le_trans _ (c3_public_guess_input_le compress i (messages i) guess)
  have equal := (c3_drop_independent_suffix ($ᵗ BitVec 128) ($ᵗ BitVec 1344)).prEvent_eq
    (fun salt => c3HiddenInput compress i (messages i) salt = guess)
  exact equal.le

private theorem c3_key_output {positions : Positions} (compress : Compression) (i : HiddenIndex positions)
    (digests : DigestTape) (messages : Index → Words 32) (guess : Block) :
    Pr{let hidden ← sampleC3HiddenTape positions}[
      (c3HiddenRow compress digests messages i (hidden i)).2 = guess] ≤ (1 : ENNReal) / 2 ^ 1344 := by
  rw [c3_coordinate_probability i (fun key => (c3HiddenRow compress digests messages i key).2 = guess)]
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [c3HiddenRow]
  apply prEvent_bind_le_of_forall_le_of_support
  intro salt _
  change Pr{let _ ← _}[_] ≤ _
  rw [bind_pure_comp, prEvent_map]
  exact public_guess_second_output_le (digests i) guess

/-- The detection rate of one query against all hidden rows: the input carries the tag of at
most one leaf and a 128-bit salt; the output must match 1344 private bits of one of at most
`2^24` replies. -/
noncomputable def c3HiddenRate : ENNReal := 1 / 2 ^ 128 + (2 ^ 24 : ENNReal) * (1 / 2 ^ 1344)

theorem c3_fixed_reference_hit_le (positions : Positions) (compress : Compression) (digests : DigestTape)
    (messages : Index → Words 32) (query : Row) :
    Pr{let hidden ← sampleC3HiddenTape positions}[
      c3HitsHidden compress digests messages query hidden] ≤ c3HiddenRate := by
  classical
  let sample := sampleC3HiddenTape positions
  let input : C3HiddenTape positions → Prop := fun hidden =>
    ∃ i : HiddenIndex positions, (c3HiddenRow compress digests messages i (hidden i)).1 = query.1
  let output (i : HiddenIndex positions) (hidden : C3HiddenTape positions) :=
    (c3HiddenRow compress digests messages i (hidden i)).2 = query.2
  have aBound : Pr{let hidden ← sample}[input hidden] ≤ (1 : ENNReal) / 2 ^ 128 := by
    apply c3_tagged_event_le (tag := fun i : HiddenIndex positions => c3Tag i.val = c3TagField query.1)
    · exact fun i j left right => Subtype.ext (c3_tag_injective (left.trans right.symm))
    · intro i hidden hit
      have tag := c3_hidden_tag compress i (messages i) (hidden i).1
      change c3HiddenInput compress i (messages i) (hidden i).1 = query.1 at hit
      rw [hit] at tag
      exact tag.symm
    · intro i
      exact c3_key_input compress i digests messages query.1
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
        Finset.sum_le_sum (fun i _ => c3_key_output compress i digests messages query.2)
      _ = (Fintype.card (HiddenIndex positions) : ENNReal) * (1 / 2 ^ 1344) := by simp [nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right castNumber zero_le
  change Pr{let hidden ← sample}[input hidden ∨ ∃ i, output i hidden] ≤ _
  exact (prEvent_or_le sample input _).trans (add_le_add aBound zBound)

theorem c3_fixed_reference_trace_hit_le (positions : Positions) (compress : Compression)
    (digests : DigestTape) (messages : Index → Words 32) (trace : List Row) :
    Pr{let hidden ← sampleC3HiddenTape positions}[
      ∃ row ∈ trace, c3HitsHidden compress digests messages row hidden] ≤
      (trace.length : ENNReal) * c3HiddenRate :=
  prEvent_list_le trace (sampleC3HiddenTape positions)
    (fun row hidden => c3HitsHidden compress digests messages row hidden)
    c3HiddenRate (fun row _ => c3_fixed_reference_hit_le positions compress digests messages row)

/-! ### Plans: one forward query per leaf -/

def c3LeafPlans (compress : Compression) (messages : Index → Words 32) (salts : Index → BitVec 128)
    (indices : List Index) : List InputPlan :=
  indices.map fun i => fun _ => c3HiddenInput compress i (messages i) (salts i)

theorem c3_leaf_plans_length (compress : Compression) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (indices : List Index) :
    (c3LeafPlans compress messages salts indices).length = indices.length := by
  simp [c3LeafPlans]

theorem c3_leaf_plan_rows_tags (compress : Compression) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (indices : List Index) (answers tape : List Block)
    (length : tape.length = indices.length) :
    (plannedRows answers (c3LeafPlans compress messages salts indices) tape).map
        (fun row => c3TagField row.1) = indices.map c3Tag := by
  induction indices generalizing answers tape with
  | nil => cases tape <;> simp [c3LeafPlans, plannedRows]
  | cons index rest ih =>
    cases tape with
    | nil => simp at length
    | cons first tail =>
      have exactTail : tail.length = rest.length := by
        simp only [List.length_cons] at length
        omega
      change c3TagField (c3HiddenInput compress index (messages index) (salts index)) ::
        (plannedRows (first :: answers) (c3LeafPlans compress messages salts rest) tail).map
          (fun row => c3TagField row.1) = c3Tag index :: rest.map c3Tag
      rw [c3_hidden_tag, ih _ _ exactTail]

theorem c3_leaf_plan_inputs_distinct (compress : Compression) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (indices : List Index) (distinct : indices.Nodup)
    (answers tape : List Block)
    (possible : tape ∈ support (sampleProposalTape (c3LeafPlans compress messages salts indices).length)) :
    ((plannedRows answers (c3LeafPlans compress messages salts indices) tape).map Prod.fst).Nodup := by
  have length := (sampleProposalTape_length possible).trans (c3_leaf_plans_length compress messages salts indices)
  have tagged : (((plannedRows answers (c3LeafPlans compress messages salts indices) tape).map Prod.fst).map
      c3TagField).Nodup := by
    rw [List.map_map]
    exact (c3_leaf_plan_rows_tags compress messages salts indices answers tape length).symm ▸
      distinct.map c3_tag_injective
  exact List.Nodup.of_map c3TagField tagged

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

abbrev C3RawTape (positions : Positions) := HiddenIndex positions → BitVec 128 × Block

def c3SplitKey : (BitVec 128 × Block) ≃ (BitVec 256 × C3Key) where
  toFun raw := (outputDigest raw.2, raw.1, raw.2.extractLsb' 256 1344)
  invFun separated := (separated.2.1, separated.2.2 ++ separated.1)
  left_inv raw := by
    obtain ⟨salt, reply⟩ := raw
    change (salt, reply.extractLsb' 256 1344 ++ reply.extractLsb' 0 256) = (salt, reply)
    have joined : reply.extractLsb' 256 1344 ++ reply.extractLsb' 0 256 = reply :=
      BitVec.extractLsb'_append_extractLsb'
    exact congrArg (fun (last : Block) => (salt, last)) joined
  right_inv separated := by
    obtain ⟨digest, salt, tail⟩ := separated
    change ((tail ++ digest).extractLsb' 0 256, salt, (tail ++ digest).extractLsb' 256 1344) =
      (digest, salt, tail)
    rw [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right]

def c3FactorReplies (positions : Positions) :
    C3RawTape positions ≃ (UnopenedDigestTape positions × C3HiddenTape positions) :=
  (Equiv.piCongrRight (fun _ : HiddenIndex positions => c3SplitKey)).trans
    (functionPairEquiv (HiddenIndex positions) (BitVec 256) C3Key)

theorem c3_expose_unopened_digests {α : Type} (positions : Positions)
    (next : UnopenedDigestTape positions → C3HiddenTape positions → ProbComp α) :
    (do let raw ← $ᵗ C3RawTape positions
        let separate := c3FactorReplies positions raw
        next separate.1 separate.2) =ᵈ
      (do let digests ← $ᵗ UnopenedDigestTape positions
          let hidden ← sampleC3HiddenTape positions
          next digests hidden) := by
  have transport := (uniform_transport_bind (transportOfEquiv (c3FactorReplies positions).symm)
    (fun pair => next pair.1 pair.2)).symm
  refine transport.trans ?_
  rw [SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  rfl

end TwoPermutationPrototype.Sampling
