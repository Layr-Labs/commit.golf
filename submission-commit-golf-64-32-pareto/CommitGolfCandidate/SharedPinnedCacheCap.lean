import CommitGolfCandidate.SharedPinnedGlobalHits

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
open scoped ENNReal
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
noncomputable local instance SharedPinnedCacheCapFunctionSampler {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _
local instance SharedPinnedCacheCapDiscrete {α : Type} : MeasurableSpace α := ⊤

section
variable {I : Type} [Fintype I] [DecidableEq I]
variable {base : Cache} {count : Nat} (state : PinnedOpenedState base count)

def sharedCachedAddresses : List Block :=
  base.entries.map Prod.fst ++ state.high.added.map PinnedHighRow.input

def SharedCachedHit (position : I → Index) (first : Bool → I → Block)
    (message : Bool → I → Words 32) (nonce : I → BitVec 128) : Prop :=
  ∃ address ∈ sharedCachedAddresses state, ∃ w i,
    pinnedPrivateSecond (position i) (first w i) (message w i) (nonce i) = address

theorem shared_cached_hit_le (position : I → Index) (unique : Function.Injective position)
    (first : Bool → I → Block) (message : Bool → I → Words 32) :
    Pr{let nonce ← $ᵗ (I → BitVec 128)}[SharedCachedHit state position first message nonce] ≤
      (state.high.zero.entries.length : ENNReal)/2^121 := by
  have bound := shared_known_address_hit_le position unique first message (sharedCachedAddresses state)
  have length : (sharedCachedAddresses state).length = state.high.zero.entries.length := by
    simp [sharedCachedAddresses, PinnedHighCache.zero, PinnedHighCache.realize, pinnedHighTable,
      Nat.add_comm]
  unfold SharedCachedHit
  rw [length] at bound
  exact bound

theorem shared_safe_added_none (position : I → Index) (first : Bool → I → Block)
    (message : Bool → I → Words 32) (nonce : I → BitVec 128)
    (safe : ¬ SharedCachedHit state position first message nonce) (w : Bool) (i : I) :
    pinnedAddedUpper state.high
      (pinnedPrivateSecond (position i) (first w i) (message w i) (nonce i)) = none := by
  classical
  unfold pinnedAddedUpper
  split
  · rename_i found
    obtain ⟨row, present, same⟩ := found
    exact (safe ⟨row.input, List.mem_append_right _ (List.mem_map.mpr ⟨row, present, rfl⟩),
      w, i, same.symm⟩).elim
  · rfl

theorem shared_safe_base (position : I → Index) (first : Bool → I → Block)
    (message : Bool → I → Words 32) (nonce : I → BitVec 128)
    (safe : ¬ SharedCachedHit state position first message nonce) (w : Bool) :
    ∀ address ∈ pinnedNonceAddresses position (first w) (message w) nonce,
      UnusedInput base.entries address := by
  intro address present row known same
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp present
  exact safe ⟨row.1, List.mem_append_left _ (List.mem_map.mpr ⟨row, known, rfl⟩),
    w, i, same.symm⟩

noncomputable def sharedGuardedNonce (position : I → Index) (first : Bool → I → Block)
    (message : Bool → I → Words 32) (digests : I → BitVec 256) (nonce : I → BitVec 128) :
    ProbComp (Bool × List Row) := by
  classical
  exact if SharedCachedHit state position first message nonce then pure (true, []) else do
    let left ← pinnedRowsNonce state position (first false) (message false) digests nonce
    let right ← pinnedRowsNonce state position (first true) (message true) digests nonce
    pure (false, left ++ right)

noncomputable def sharedGuardedRows (position : I → Index) (first : Bool → I → Block)
    (message : Bool → I → Words 32) (digests : I → BitVec 256) : ProbComp (Bool × List Row) :=
  ($ᵗ (I → BitVec 128)) >>= sharedGuardedNonce state position first message digests

attribute [local irreducible] pinnedRowsNonce

theorem shared_guarded_rows_hit (valid : state.high.Valid count)
    (position : I → Index) (unique : Function.Injective position)
    (first : Bool → I → Block) (message : Bool → I → Words 32) (digests : I → BitVec 256)
    (room : state.high.zero.entries.length + Fintype.card I ≤ 2^121) (query : Row) :
    Pr{let draw ← sharedGuardedRows state position first message digests}[
      draw.1 = false ∧ rowHits draw.2 query = true] ≤
      1/2^121 + 2*(Fintype.card I : ENNReal)/2^1343 := by
  classical
  let hit (nonce : I → BitVec 128) := ∃ w i,
    pinnedPrivateSecond (position i) (first w i) (message w i) (nonce i) = query.1
  have initial := shared_fixed_address_hit_le position unique first message query.1
  have after (nonce : I → BitVec 128) (_ : nonce ∈ support ($ᵗ (I → BitVec 128)))
      (noInput : ¬hit nonce) :
      Pr{let draw ← sharedGuardedNonce state position first message digests nonce}[
        draw.1 = false ∧ rowHits draw.2 query = true] ≤ 2*(Fintype.card I : ENNReal)/2^1343 := by
    by_cases cached : SharedCachedHit state position first message nonce
    · simp [sharedGuardedNonce, cached]
    · have per (w : Bool) :
          Pr{let rows ← pinnedRowsNonce state position (first w) (message w) digests nonce}[
            rowHits rows query = true] ≤ (Fintype.card I : ENNReal)/2^1343 := by
        apply rows_nonce_fresh_hit_le state valid position (first w) (message w) digests room query nonce
        rintro (⟨i, input⟩ | ⟨i, output⟩)
        · exact noInput ⟨w, i, input⟩
        · rw [shared_safe_added_none state position first message nonce cached w i] at output
          cases output
      have shape : sharedGuardedNonce state position first message digests nonce =
          (pinnedRowsNonce state position (first false) (message false) digests nonce >>= fun left =>
            (fun right => ((false, left ++ right) : Bool × List Row)) <$>
              pinnedRowsNonce state position (first true) (message true) digests nonce) := by
        rw [sharedGuardedNonce, if_neg cached]
        simp only [map_eq_bind_pure_comp]
        rfl
      rw [shape]
      have bound := prEvent_bind_le_prEvent_add_of_support
        (pinnedRowsNonce state position (first false) (message false) digests nonce)
        (fun left => (fun right => ((false, left ++ right) : Bool × List Row)) <$>
          pinnedRowsNonce state position (first true) (message true) digests nonce)
        (fun left => rowHits left query = true)
        (fun draw => draw.1 = false ∧ rowHits draw.2 query = true) (by
          intro left _ off
          have clear : rowHits left query = false := Bool.eq_false_iff.mpr off
          simp only [rowHits] at clear
          simpa only [prEvent_map, true_and, rowHits, List.any_append, clear, Bool.false_or]
            using per true)
      have twice : (Fintype.card I : ENNReal)/2^1343 + (Fintype.card I : ENNReal)/2^1343 =
          2*(Fintype.card I : ENNReal)/2^1343 := by
        simp only [div_eq_mul_inv]
        ring
      exact bound.trans ((add_le_add (per false) le_rfl).trans_eq twice)
  exact (prEvent_bind_le_prEvent_add_of_support ($ᵗ (I → BitVec 128))
    (sharedGuardedNonce state position first message digests) hit
    (fun draw => draw.1 = false ∧ rowHits draw.2 query = true) after).trans
      (add_le_add initial le_rfl)

theorem shared_guarded_rows_bad (position : I → Index) (unique : Function.Injective position)
    (first : Bool → I → Block) (message : Bool → I → Words 32) (digests : I → BitVec 256) :
    Pr{let draw ← sharedGuardedRows state position first message digests}[draw.1 = true] ≤
      (state.high.zero.entries.length : ENNReal)/2^121 := by
  classical
  have after (nonce : I → BitVec 128) (_ : nonce ∈ support ($ᵗ (I → BitVec 128)))
      (safe : ¬SharedCachedHit state position first message nonce) :
      Pr{let draw ← sharedGuardedNonce state position first message digests nonce}[draw.1 = true] ≤ 0 := by
    rw [prEvent_eq_zero_of_forall_mem_support _ _ (by
      intro draw reached hit
      rw [sharedGuardedNonce, if_neg safe] at reached
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
      obtain ⟨left, _, right, _, rfl⟩ := reached
      cases hit)]
  have bound := prEvent_bind_le_prEvent_add_of_support ($ᵗ (I → BitVec 128))
    (sharedGuardedNonce state position first message digests)
    (SharedCachedHit state position first message) (fun draw => draw.1 = true) after
  exact bound.trans (by simpa only [add_zero] using shared_cached_hit_le state position unique first message)

end
end TwoPermutationPrototype.Sampling
