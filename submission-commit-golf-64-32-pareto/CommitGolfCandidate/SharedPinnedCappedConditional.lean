import CommitGolfCandidate.SharedPinnedPairCoupling

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
open scoped ENNReal
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
noncomputable local instance SharedPinnedCappedConditionalFunctionSampler {ι α : Type}
    [Fintype ι] [Fintype α] [Nonempty α] : SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _
local instance SharedPinnedCappedConditionalDiscrete {α : Type} : MeasurableSpace α := ⊤

section
variable {I : Type} [Fintype I] [DecidableEq I]
variable {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
variable [DecidablePred state.isRevealed]
variable (opened : {i : Fin count // state.isRevealed i} → BitVec 256)
variable (position : I → Index) (first : Bool → I → Block) (message : Bool → I → Words 32)
variable {Output : Type} (compress : Compression) (observer : (I → BitVec 256) → OracleComp World Output)

noncomputable def sharedConditionalFlagged (nonce : I → BitVec 128) : ProbComp (Output × Unit × Bool) := do
  let digest ← samplePinnedLowFn I
  let p ← samplePinnedBasePermutation state opened
  let draw ← sharedGuardedNonce state position first message digest nonce
  flaggedRun (fixedOracle compress p) (marksReferencePair p draw.2) (observer digest) draw.1

theorem shared_conditional_cached_flag (nonce : I → BitVec 128)
    (cached : SharedCachedHit state position first message nonce) :
    Pr{let result ← sharedConditionalFlagged state opened position first message compress observer nonce}[
      result.2.2 = true] = 1 := by
  classical
  apply prEvent_eq_one_of_forall_mem_support
  intro result reached
  simp only [sharedConditionalFlagged, sharedGuardedNonce, if_pos cached, pure_bind,
    flagged_reference_trace, Bool.true_or] at reached
  simp only [mem_support_bind_iff, support_map, Set.mem_image] at reached
  obtain ⟨digest, _, p, _, trace, _, rfl⟩ := reached
  rfl

attribute [local irreducible] pinnedRowsNonce

theorem shared_conditional_exception_distance (valid : state.high.Valid count)
    (unique : Function.Injective position)
    (room : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (disjoint : ∀ w nonce address,
      address ∈ pinnedNonceAddresses position (first w) (message w) nonce → address ∉ state.opened) :
    let execute := fun digest p => fixedOracleRun (fixedOracle compress p) (observer digest)
    measureETVDist
      (pinnedConditionalActual state opened position (first false) (message false) execute)
      (pinnedConditionalActual state opened position (first true) (message true) execute) ≤
      Pr{let result ← (($ᵗ (I → BitVec 128)) >>=
        sharedConditionalFlagged state opened position first message compress observer)}[result.2.2 = true] := by
  classical
  let execute := fun digest p => fixedOracleRun (fixedOracle compress p) (observer digest)
  change measureETVDist
    (($ᵗ (I → BitVec 128)) >>= pinnedActualNonce state opened position (first false) (message false) execute)
    (($ᵗ (I → BitVec 128)) >>= pinnedActualNonce state opened position (first true) (message true) execute) ≤ _
  apply distance_averaged_event ($ᵗ (I → BitVec 128)) _ _
    (sharedConditionalFlagged state opened position first message compress observer) (fun result => result.2.2 = true)
  intro nonce
  by_cases cached : SharedCachedHit state position first message nonce
  · rw [shared_conditional_cached_flag state opened position first message compress observer nonce cached]
    exact measureETVDist_le_one _ _
  · have left := pinned_actual_nonce_programmed state opened position (first false) (message false)
      execute valid unique nonce room (disjoint false nonce)
      (shared_safe_base state position first message nonce cached false)
    have right := pinned_actual_nonce_programmed state opened position (first true) (message true)
      execute valid unique nonce room (disjoint true nonce)
      (shared_safe_base state position first message nonce cached true)
    unfold measureETVDist
    rw [left.evalDist_eq, right.evalDist_eq]
    change measureETVDist
      (pinnedProgrammedNonce state opened position (first false) (message false) execute nonce)
      (pinnedProgrammedNonce state opened position (first true) (message true) execute nonce) ≤ _
    unfold pinnedProgrammedNonce sharedConditionalFlagged
    apply distance_averaged_event (samplePinnedLowFn I) _ _ _
      (fun result : Output × Unit × Bool => result.2.2 = true)
    intro digest
    apply distance_averaged_event (samplePinnedBasePermutation state opened) _ _ _
      (fun result : Output × Unit × Bool => result.2.2 = true)
    intro p
    rw [sharedGuardedNonce, if_neg cached]
    simpa only [execute, bind_assoc, pure_bind] using shared_product_reference_hit
      (pinnedRowsNonce state position (first false) (message false) digest nonce)
      (pinnedRowsNonce state position (first true) (message true) digest nonce) compress p (observer digest)

theorem shared_conditional_flagged_bound (valid : state.high.Valid count)
    (unique : Function.Injective position)
    (room : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (budget : Nat) (bounded : ∀ digest, QueryBounded (observer digest) budget) :
    Pr{let result ← (($ᵗ (I → BitVec 128)) >>=
      sharedConditionalFlagged state opened position first message compress observer)}[result.2.2 = true] ≤
      (state.high.zero.entries.length : ENNReal)/2^121 +
        (budget : ENNReal)*(1/2^121 + 2*(Fintype.card I : ENNReal)/2^1343) := by
  let finish (nonce : I → BitVec 128) (digest : I → BitVec 256) (p : BiPermutation Block) := do
    let draw ← sharedGuardedNonce state position first message digest nonce
    flaggedRun (fixedOracle compress p) (marksReferencePair p draw.2) (observer digest) draw.1
  let ordered : ProbComp (Output × Unit × Bool) := do
    let digest ← samplePinnedLowFn I
    let p ← samplePinnedBasePermutation state opened
    let nonce ← $ᵗ (I → BitVec 128)
    finish nonce digest p
  have reorder : (($ᵗ (I → BitVec 128)) >>=
      sharedConditionalFlagged state opened position first message compress observer) =ᵈ ordered := by
    change (do
      let nonce ← $ᵗ (I → BitVec 128)
      let digest ← samplePinnedLowFn I
      let p ← samplePinnedBasePermutation state opened
      finish nonce digest p) =ᵈ _
    apply (EvalDistEq.of_evalDist_eq (distribution_bind_comm ($ᵗ (I → BitVec 128))
      (samplePinnedLowFn I) (fun nonce digest => do
        let p ← samplePinnedBasePermutation state opened
        finish nonce digest p))).trans
    apply EvalDistEq.bind_right
    intro digest
    exact EvalDistEq.of_evalDist_eq (distribution_bind_comm ($ᵗ (I → BitVec 128))
      (samplePinnedBasePermutation state opened) (fun nonce p => finish nonce digest p))
  rw [reorder.prEvent_eq (fun result => result.2.2 = true)]
  apply prEvent_bind_le_of_forall_le_of_support
  intro digest _
  apply prEvent_bind_le_of_forall_le_of_support
  intro p _
  have bound := shared_exceptional_reference_hits (sharedGuardedRows state position first message digest)
    (1/2^121 + 2*(Fintype.card I : ENNReal)/2^1343) compress p (observer digest) budget
    (bounded digest) (shared_guarded_rows_hit state valid position unique first message digest room)
  have enlarged := bound.trans (add_le_add
    (shared_guarded_rows_bad state position unique first message digest) le_rfl)
  simpa only [finish, sharedGuardedRows, bind_assoc] using enlarged

theorem shared_conditional_capped_distance (valid : state.high.Valid count)
    (unique : Function.Injective position)
    (room : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (disjoint : ∀ w nonce address,
      address ∈ pinnedNonceAddresses position (first w) (message w) nonce → address ∉ state.opened)
    (budget : Nat) (bounded : ∀ digest, QueryBounded (observer digest) budget) :
    let execute := fun digest p => fixedOracleRun (fixedOracle compress p) (observer digest)
    measureTVDist
      (pinnedConditionalActual state opened position (first false) (message false) execute)
      (pinnedConditionalActual state opened position (first true) (message true) execute) ≤
      (state.high.zero.entries.length : ℝ)/2^121 +
        (budget : ℝ)*(1/2^121 + 2*(Fintype.card I : ℝ)/2^1343) := by
  have bound := (shared_conditional_exception_distance state opened position first message compress observer
    valid unique room disjoint).trans
    (shared_conditional_flagged_bound state opened position first message compress observer
      valid unique room budget bounded)
  dsimp only
  rw [measureTVDist_eq_toReal_measureETVDist]
  have real := ENNReal.toReal_mono (by finiteness) bound
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at real
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at real
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at real
  simpa only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one] using real

end
end TwoPermutationPrototype.Sampling
