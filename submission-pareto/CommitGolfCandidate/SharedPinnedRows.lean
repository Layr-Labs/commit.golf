import CommitGolfCandidate.SharedNonceHits
import CommitGolfCandidate.TaggedPinnedConditionalObserver

/-! Coupled hidden-row samples using one nonce tape in both message worlds. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 2048
noncomputable local instance SharedPinnedRowsFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _
local instance SharedPinnedRowsDiscrete {α : Type} : MeasurableSpace α := ⊤

section
variable {I : Type} [Fintype I]
variable {base : Cache} {count : Nat} (state : PinnedOpenedState base count)

noncomputable def sharedPinnedRows (position : I → Index) (first : Bool → I → Block)
    (message : Bool → I → Words 32) (digests : I → BitVec 256) : ProbComp (List Row × List Row) := do
  let nonce ← $ᵗ (I → BitVec 128)
  let left ← pinnedRowsNonce state position (first false) (message false) digests nonce
  let right ← pinnedRowsNonce state position (first true) (message true) digests nonce
  pure (left, right)

theorem rows_nonce_sampler (position : I → Index) (first : I → Block)
    (message : I → Words 32) (digests : I → BitVec 256) :
    samplePinnedHiddenRows state.high count position first message digests =
      (($ᵗ (I → BitVec 128)) >>= pinnedRowsNonce state position first message digests) := rfl

theorem shared_rows_left {α : Type} (position : I → Index) (first : Bool → I → Block)
    (message : Bool → I → Words 32) (digests : I → BitVec 256) (next : List Row → ProbComp α) :
    (sharedPinnedRows state position first message digests >>= fun rows => next rows.1) =ᵈ
      (samplePinnedHiddenRows state.high count position (first false) (message false) digests >>= next) := by
  rw [rows_nonce_sampler]
  unfold sharedPinnedRows
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro nonce
  apply EvalDistEq.bind_right
  intro left
  exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const
    (pinnedRowsNonce state position (first true) (message true) digests nonce) (next left))

theorem shared_rows_right {α : Type} (position : I → Index) (first : Bool → I → Block)
    (message : Bool → I → Words 32) (digests : I → BitVec 256) (next : List Row → ProbComp α) :
    (sharedPinnedRows state position first message digests >>= fun rows => next rows.2) =ᵈ
      (samplePinnedHiddenRows state.high count position (first true) (message true) digests >>= next) := by
  rw [rows_nonce_sampler]
  unfold sharedPinnedRows
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro nonce
  exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const
    (pinnedRowsNonce state position (first false) (message false) digests nonce)
    (pinnedRowsNonce state position (first true) (message true) digests nonce >>= next))

theorem rows_nonce_fresh_hit_le (valid : state.high.Valid count)
    (position : I → Index)
    (first : I → Block) (message : I → Words 32) (digests : I → BitVec 256)
    (room : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (query : Row) (nonce : I → BitVec 128)
    (safe : ¬ ((∃ i, pinnedPrivateSecond (position i) (first i) (message i) (nonce i) = query.1) ∨
      ∃ i, (pinnedAddedUpper state.high
        (pinnedPrivateSecond (position i) (first i) (message i) (nonce i))).map
        (fun upper => (upper ++ digests i : Block)) = some query.2)) :
    Pr{let rows ← pinnedRowsNonce state position first message digests nonce}[rowHits rows query = true] ≤
      (Fintype.card I : ENNReal)/2^1343 := by
  classical
  let b (nonce : I → BitVec 128) (i : I) := pinnedPrivateSecond (position i) (first i) (message i) (nonce i)
  let addresses := pinnedNonceAddresses position first message nonce
  let plans := pinnedConstantPlans addresses
  let run := runPinnedHigh state.high count [] plans
  let made (final : List (BitVec 1344) × PinnedHighCache base) : List Row :=
    Finset.univ.toList.map (fun i =>
      let input := b nonce i
      (input, pinnedCachedUpper final.2.zero input ++ digests i))
  have shape : pinnedRowsNonce state position first message digests nonce = (if ∀ input ∈ addresses, UnusedInput base.entries input then
    run >>= fun final => pure (made final) else pure []) := rfl
  by_cases new : ∀ input ∈ addresses, UnusedInput base.entries input
  · rw [shape, ite_eq_left new, bind_pure_comp, prEvent_map]
    have size : plans.length = Fintype.card I := by
      simp only [plans, pinnedConstantPlans, List.length_map, addresses, pinned_nonce_addresses_length]
    have enough : state.high.zero.entries.length + plans.length ≤ 2^121 := size ▸ room
    have tailBound := pinned_high_new_tail_le state.high count [] plans enough (pinnedOutputTail query.2)
    have returnBound : Pr{let final ← run}[state.high.NewTail final.2 (pinnedOutputTail query.2)] ≤
        (Fintype.card I : ENNReal)/2^1343 := by
      simpa only [size, run] using tailBound
    refine (prEvent_mono_of_support run (p := fun final => rowHits (made final) query = true)
      (q := fun final => state.high.NewTail final.2 (pinnedOutputTail query.2)) ?_).trans returnBound
    intro final reached detected
    simp only [made, rowHits, List.any_eq_true, List.mem_map, Finset.mem_toList, Finset.mem_univ,
      true_and, decide_eq_true_eq] at detected
    obtain ⟨_, ⟨i, rfl⟩, input | output⟩ := detected
    · exact (safe (Or.inl ⟨i, input.symm⟩)).elim
    · have here : b nonce i ∈ addresses := List.mem_map.mpr ⟨i, by simp, rfl⟩
      have fact := pinned_high_const_support state.high count [] addresses valid
        (by simpa only [addresses, pinned_nonce_addresses_length] using room) final reached
      obtain ⟨stored, appears, equal⟩ := pinned_row_from_covers final.2 (b nonce i)
        (fact.2.2.2 (b nonce i) here) (new _ here)
      have top := pinned_high_cached_upper_of_row final.2 stored appears
      rw [equal] at top
      have bytes : (stored.upper ++ digests i : Block) = query.2 :=
        (congrArg (fun head : BitVec 1344 => (head ++ digests i : Block)) top).symm.trans output.symm
      by_cases wasStored : stored ∈ state.high.added
      · have initial := pinned_added_upper_read state.high valid stored wasStored
        rw [equal] at initial
        exact (safe (Or.inr ⟨i, by
          rw [initial]; exact congrArg some bytes⟩)).elim
      · have replyTail : pinnedOutputTail (stored.upper ++ digests i) = stored.upper :=
          BitVec.extractLsb'_append_eq_left
        exact ⟨stored, appears, wasStored, replyTail.symm.trans (congrArg pinnedOutputTail bytes)⟩
  · rw [shape, ite_eq_right new]
    simp [rowHits]

attribute [local irreducible] pinnedRowsNonce

theorem shared_rows_hit_le (valid : state.high.Valid count)
    (position : I → Index) (different : Function.Injective position)
    (first : Bool → I → Block) (message : Bool → I → Words 32) (digests : I → BitVec 256)
    (room : state.high.zero.entries.length + Fintype.card I ≤ 2^121) (query : Row) :
    Pr{let pair ← sharedPinnedRows state position first message digests}[
      rowHits (pair.1 ++ pair.2) query = true] ≤
      2/2^121 + 2*(Fintype.card I : ENNReal)/2^1343 := by
  classical
  let b (nonce : I → BitVec 128) (w : Bool) (i : I) :=
    pinnedPrivateSecond (position i) (first w i) (message w i) (nonce i)
  let inputHit (nonce : I → BitVec 128) := ∃ w i, b nonce w i = query.1
  let oldHit (nonce : I → BitVec 128) := ∃ w i,
    (pinnedAddedUpper state.high (b nonce w i)).map (fun hi => (hi ++ digests i : Block)) = some query.2
  let bad (nonce : I → BitVec 128) := inputHit nonce ∨ oldHit nonce
  have badBound : Pr{let nonce ← $ᵗ (I → BitVec 128)}[bad nonce] ≤ (2 : ENNReal)/2^121 := by
    have inputBound := shared_fixed_address_hit_le position different first message query.1
    have oldBound := shared_reused_output_hit_le position different first message
      (pinnedAddedUpper state.high) (pinned_added_upper_injective state.high valid) digests query.2
    exact (prEvent_or_le ($ᵗ (I → BitVec 128)) inputHit oldHit).trans
      ((add_le_add inputBound oldBound).trans_eq (by simp only [div_eq_mul_inv]; ring))
  let observe (nonce : I → BitVec 128) : ProbComp (List Row × List Row) := do
    let left ← pinnedRowsNonce state position (first false) (message false) digests nonce
    let right ← pinnedRowsNonce state position (first true) (message true) digests nonce
    pure (left, right)
  have after (nonce : I → BitVec 128) (_ : nonce ∈ support ($ᵗ (I → BitVec 128))) (safe : ¬bad nonce) :
      Pr{let pair ← observe nonce}[rowHits (pair.1 ++ pair.2) query = true] ≤
        2*(Fintype.card I : ENNReal)/2^1343 := by
    have per (w : Bool) :
        Pr{let rows ← pinnedRowsNonce state position (first w) (message w) digests nonce}[
          rowHits rows query = true] ≤ (Fintype.card I : ENNReal)/2^1343 := by
      apply rows_nonce_fresh_hit_le state valid position (first w) (message w) digests room query nonce
      rintro (⟨i, hit⟩ | ⟨i, hit⟩)
      · exact safe (Or.inl ⟨w, i, hit⟩)
      · exact safe (Or.inr ⟨w, i, hit⟩)
    have step := prEvent_bind_le_prEvent_add_of_support
      (pinnedRowsNonce state position (first false) (message false) digests nonce)
      (fun left => (fun right => (left, right)) <$>
        pinnedRowsNonce state position (first true) (message true) digests nonce)
      (fun left => rowHits left query = true)
      (fun pair => rowHits (pair.1 ++ pair.2) query = true)
      (by
        intro left _ good
        simp only [prEvent_map]
        have off : rowHits left query = false := Bool.eq_false_iff.mpr good
        simp only [rowHits] at off
        simpa only [rowHits, List.any_append, off, Bool.false_or] using per true)
    have twice : (Fintype.card I : ENNReal)/2^1343 + (Fintype.card I : ENNReal)/2^1343 =
        2*(Fintype.card I : ENNReal)/2^1343 := by
      simp only [div_eq_mul_inv]
      ring
    have combined := step.trans (add_le_add (per false)
      (le_refl ((Fintype.card I : ENNReal)/2^1343)))
    rw [twice] at combined
    simpa only [observe, map_eq_bind_pure_comp, Function.comp_def] using combined
  exact (prEvent_bind_le_prEvent_add_of_support ($ᵗ (I → BitVec 128)) observe bad
    (fun pair => rowHits (pair.1 ++ pair.2) query = true) after).trans
    (add_le_add badBound le_rfl)

end
end TwoPermutationPrototype.Sampling
