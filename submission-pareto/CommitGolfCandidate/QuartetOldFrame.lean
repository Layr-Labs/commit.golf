import CommitGolfCandidate.QuartetRestricted
import CommitGolfCandidate.QuadReplay

namespace TwoPermutationPrototype.Sampling.Quartet
open CommitGolf OracleComp CommitGolfCandidate

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 2048
open scoped ENNReal
local instance QuartetOldFrameLocalInstance1 {α : Type} : MeasurableSpace α := ⊤

theorem quartet_domain_mem {x : Block} : x ∈ quartetDomain ↔ x ∈ quadDomain := by
  classical
  constructor
  · intro hit
    obtain ⟨payload, _, equal⟩ := List.mem_map.mp hit
    exact ⟨payload,equal⟩
  · rintro ⟨payload,equal⟩
    exact List.mem_map.mpr ⟨payload,by simp,equal⟩

theorem cached_old_match_must_be_fresh {base : Cache} (cache : PinnedHighCache base)
    (slot : Nat) (valid : cache.Valid slot) (low : PinnedLowTape)
    (p : Completion (cache.realize low).entries) (x : Block) (old : PinnedHighRow) (present : old ∈ cache.added)
    (different : x ≠ old.input) (matching : pinnedOutputTail (p.val.forward x) = old.upper) :
    UnusedOutput (cache.realize low).entries (p.val.forward x) := by
  classical
  intro q inside same
  change q ∈ cache.added.map (fun r => r.realize low) ++ base.entries at inside
  rcases List.mem_append.mp inside with staged | chooser
  · obtain ⟨other, stored, rfl⟩ := List.mem_map.mp staged
    have high : other.upper = old.upper :=
      (pinned_high_row_tail other low).symm.trans ((congrArg pinnedOutputTail same).trans matching)
    have equal := pinned_unique_mapped_key PinnedHighRow.upper valid.tailUnique stored present high
    subst other
    have known := p.property (old.realize low) (List.mem_append_left _ (List.mem_map_of_mem present))
    have agrees : p.val.forward old.input = p.val.forward x := known.trans same
    have sameInput := congrArg p.val.inverse agrees
    rw [p.val.leftInverse, p.val.leftInverse] at sameInput
    exact different sameInput.symm
  · apply valid.chooserTail old present
    exact List.mem_map.mpr ⟨q,chooser,(congrArg pinnedOutputTail same).trans matching⟩

theorem old_tails_at_realization {base : Cache} (cache : PinnedHighCache base) (slot : Nat)
    (valid : cache.Valid slot) (low : PinnedLowTape) (room : cache.zero.entries.length ≤ 2^121) :
    Pr{let p ← (cache.realize low).sample}[¬ PreservesOldTails cache p.val quartetDomain] ≤
      (1:ENNReal)/2^198 := by
  classical
  let known := cache.realize low
  let highs := cache.added.map PinnedHighRow.upper
  have sameLen : known.entries.length = cache.zero.entries.length := by
    rw [show known = cache.realize low from rfl, PinnedHighCache.entries_length]
    exact (cache.entries_length (fun _ => 0)).symm
  have fits : known.entries.length ≤ 2^121 := sameLen.trans_le room
  have listSize : highs.length ≤ 2^121 := by
    rw [show cache.zero.entries.length = _ from cache.entries_length (fun _ => 0)] at room
    simp only [highs, List.length_map]
    omega
  let event (h : BitVec 1344) (p : Completion known.entries) :=
    ∃ lo : BitVec 256, UnusedOutput known.entries (h ++ lo) ∧ p.val.inverse (h ++ lo) ∈ quadDomain
  have all := prEvent_list_le highs known.sample event ((1:ENNReal)/2^319)
    (fun hi _ => quad_fresh_variant_preimage_prob known hi fits)
  have tiny : (highs.length:ENNReal) * (1/2^319) ≤ (1:ENNReal)/2^198 := by
    have h : (highs.length:ENNReal) ≤ (2:ENNReal)^121 := by exact_mod_cast listSize
    apply (mul_le_mul_of_nonneg_right h (by positivity : (0:ENNReal) ≤ 1/2^319)).trans
    rw [show (2:ENNReal)^319 = 2^198 * 2^121 from pow_add _ 198 121]
    simpa only [div_eq_mul_inv,one_mul] using
      (ENNReal.mul_div_mul_right (c := (2:ENNReal)^121) 1 (2^198) (by positivity) (by finiteness)).le
  apply (prEvent_mono known.sample (p := fun p => ¬ PreservesOldTails cache p.val quartetDomain)
    (q := fun p => ∃ high ∈ highs, event high p) ?_).trans (all.trans tiny)
  intro p broken
  unfold PreservesOldTails at broken
  push Not at broken
  obtain ⟨x, member, old, stored, different, high⟩ := broken
  let target := p.val.forward x
  have split : (old.upper ++ pinnedOutputDigest target : Block) = target := by
    rw [← high]
    exact BitVec.extractLsb'_append_extractLsb'
  refine ⟨old.upper, List.mem_map.mpr ⟨old,stored,rfl⟩,pinnedOutputDigest target,?_,?_⟩
  · rw [split]
    exact cached_old_match_must_be_fresh cache slot valid low p x old stored different high
  · rw [split,show p.val.inverse target=x from p.val.leftInverse x]
    exact quartet_domain_mem.mp member

theorem old_base_permutation {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) [DecidablePred state.isRevealed]
    (valid : state.high.Valid count) (opened : {i : Fin count // state.isRevealed i} → BitVec 256)
    (room : state.high.zero.entries.length ≤ 2^121) :
    Pr{let p ← samplePinnedBasePermutation state opened}[¬ PreservesOldTails state.high p quartetDomain] ≤
      (1:ENNReal)/2^198 := by
  unfold samplePinnedBasePermutation
  apply prEvent_bind_le_of_forall_le_of_support
  intro priv _
  rw [bind_pure_comp,prEvent_map]
  exact old_tails_at_realization state.high count valid (pinnedFinLowTape (state.merge opened priv)) room

theorem global_frame : GlobalFrame := by
  intro I _ _ base count state _ valid opened position first message room sites digest
  have separate (nonce : I → BitVec 128) (x : Block) (inside : x ∈ quartetDomain) (i : I) :
      x ≠ pinnedPrivateSecond (position i) (first i) (message i) (nonce i) := by
    intro eq
    have mem := quartet_domain_mem.mp inside
    rw [eq] at mem
    exact quad_domain_disjoint_private (position i) (saltWords (nonce i)) (first i) (message i) mem
  have both := hidden_program_average state.high count valid position first message digest room
    (samplePinnedBasePermutation state opened) quartetDomain separate (1/2^198)
    (old_base_permutation state valid opened (by omega))
  apply both.trans
  rw [quartet_domain_size]
  have cap : (Fintype.card I : ENNReal) ≤ 2^24 := by exact_mod_cast sites
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  calc
    _ ≤ (1:ENNReal)/2^198 + 2^1024 * (2^24/2^1343) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (ENNReal.div_le_div_right cap _) zero_le)
    _ ≤ _ := by
      rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow]

end TwoPermutationPrototype.Sampling.Quartet
