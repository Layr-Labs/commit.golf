import CommitGolfCandidate.TaggedPinnedHiddenRows

namespace TwoPermutationPrototype.Sampling.Quartet
open CommitGolf OracleComp TwoPermutationPrototype

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option exponentiation.threshold 2048

/-- A four-child input has one free 1024-bit payload with 576 low zero bits. -/
noncomputable def quartetDomain : List Block :=
  (Finset.univ : Finset (BitVec 1024)).toList.map (fun payload => (payload ++ (0 : BitVec 576) : Block))

theorem quartet_domain_size : quartetDomain.length = 2^1024 := by
  simp [quartetDomain, Fintype.card_bitVec]

/-- Every cached latent row whose input is different from a domain point has
a different output high part from that point. This also covers raw first
inputs that are themselves valid quartet inputs. -/
def PreservesOldTails {base : Cache} (cache : PinnedHighCache base) (p : BiPermutation Block)
    (domain : List Block) : Prop :=
  ∀ x ∈ domain, ∀ row ∈ cache.added, x ≠ row.input → pinnedOutputTail (p.forward x) ≠ row.upper

/-- The targets can be selected after fixing the original (unprogrammed)
permutation. Taking its image requires no public oracle budget here. -/
theorem fresh_tail_hits_domain {base : Cache} (cache : PinnedHighCache base) (slot : Nat)
    (answers : List (BitVec 1344)) (plans : List PinnedHighPlan)
    (room : cache.zero.entries.length + plans.length ≤ 2^121)
    (p : BiPermutation Block) (domain : List Block) :
    Pr{let result ← runPinnedHigh cache slot answers plans}[
      ∃ x ∈ domain, cache.NewTail result.2 (pinnedOutputTail (p.forward x))] ≤
        (domain.length : ENNReal) * ((plans.length : ENNReal)/2^1343) :=
  prEvent_list_le domain (runPinnedHigh cache slot answers plans)
    (fun x result => cache.NewTail result.2 (pinnedOutputTail (p.forward x))) _
    (fun _ _ => pinned_high_new_tail_le cache slot answers plans room _)

noncomputable def generatedRows {I : Type} [Fintype I] {base : Cache} (finish : PinnedHighCache base)
    (position : I → Index) (first : I → Block) (message : I → Words 32)
    (digest : I → BitVec 256) (nonce : I → BitVec 128) : List Row := by
  classical
  exact Finset.univ.toList.map fun i =>
    let input := pinnedPrivateSecond (position i) (first i) (message i) (nonce i)
    (input, pinnedCachedUpper finish.zero input ++ digest i)

theorem generated_rows_preserve_domain {I : Type} [Fintype I] {base : Cache}
    (cache : PinnedHighCache base) (slot : Nat) (valid : cache.Valid slot)
    (position : I → Index) (first : I → Block) (message : I → Words 32)
    (digest : I → BitVec 256) (nonce : I → BitVec 128)
    (room : cache.zero.entries.length + Fintype.card I ≤ 2^121)
    (p : BiPermutation Block) (domain : List Block)
    (isolated : ∀ x ∈ domain, ∀ i, x ≠ pinnedPrivateSecond (position i) (first i) (message i) (nonce i))
    (safe : ∀ addr ∈ pinnedNonceAddresses position first message nonce, UnusedInput base.entries addr)
    (old : PreservesOldTails cache p domain)
    (result : List (BitVec 1344) × PinnedHighCache base)
    (reached : result ∈ support (runPinnedHigh cache slot []
      (pinnedConstantPlans (pinnedNonceAddresses position first message nonce))))
    (new : ¬ ∃ x ∈ domain, cache.NewTail result.2 (pinnedOutputTail (p.forward x))) :
    ∀ x ∈ domain, (p.programRows (generatedRows result.2 position first message digest nonce)).forward x =
        p.forward x := by
  classical
  let addresses := pinnedNonceAddresses position first message nonce
  have enough : cache.zero.entries.length + addresses.length ≤ 2^121 := by
    simpa only [addresses,pinned_nonce_addresses_length] using room
  have provenance := pinned_high_const_support cache slot [] addresses valid enough result reached
  intro x requested
  apply p.program_rows_forward_unchanged
  intro row inside
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp inside
  let input := pinnedPrivateSecond (position i) (first i) (message i) (nonce i)
  have present : input ∈ addresses := List.mem_map.mpr ⟨i, by simp, rfl⟩
  obtain ⟨stored, logged, equal⟩ := pinned_row_from_covers result.2 input
    (provenance.2.2.2 input present) (safe _ present)
  refine ⟨isolated _ requested i, ?_⟩
  change p.forward x ≠ (pinnedCachedUpper result.2.zero input ++ digest i : Block)
  intro hit
  have read := pinned_high_cached_upper_of_row result.2 stored logged
  rw [equal] at read
  have high : pinnedOutputTail (p.forward x) = stored.upper := by
    rw [hit]
    exact BitVec.extractLsb'_append_eq_left.trans read
  by_cases known : stored ∈ cache.added
  · exact old x requested stored known (equal.symm ▸ isolated x requested i) high
  · exact new ⟨x, requested, stored, logged, known, high.symm⟩

theorem hidden_program_frame_probability {I : Type} [Fintype I] {base : Cache}
    (cache : PinnedHighCache base) (slot : Nat) (valid : cache.Valid slot)
    (position : I → Index) (first : I → Block) (message : I → Words 32)
    (digest : I → BitVec 256) (room : cache.zero.entries.length + Fintype.card I ≤ 2^121)
    (p : BiPermutation Block) (domain : List Block)
    (isolated : ∀ nonce : I → BitVec 128, ∀ x ∈ domain, ∀ i,
      x ≠ pinnedPrivateSecond (position i) (first i) (message i) (nonce i))
    (old : PreservesOldTails cache p domain) :
    Pr{let rows ← samplePinnedHiddenRows cache slot position first message digest}[
      ∃ x ∈ domain, (p.programRows rows).forward x ≠ p.forward x] ≤
        (domain.length : ENNReal) * ((Fintype.card I : ENNReal)/2^1343) := by
  classical
  unfold samplePinnedHiddenRows
  apply prEvent_bind_le_of_forall_le_of_support
  intro nonce _
  let addresses := pinnedNonceAddresses position first message nonce
  let plans := pinnedConstantPlans addresses
  have length : plans.length = Fintype.card I := by
    simp only [plans, addresses, pinnedConstantPlans, List.length_map, pinned_nonce_addresses_length]
  have enough : cache.zero.entries.length + plans.length ≤ 2^121 := length ▸ room
  by_cases safe : ∀ addr ∈ addresses, UnusedInput base.entries addr
  · rw [ite_eq_left safe, bind_pure_comp, prEvent_map]
    have chance := fresh_tail_hits_domain cache slot [] plans enough p domain
    rw [length] at chance
    refine (prEvent_mono_of_support (runPinnedHigh cache slot [] plans)
      (p := fun final => ∃ x ∈ domain, (p.programRows (generatedRows final.2 position first message digest nonce)).forward x ≠ p.forward x)
      (q := fun final => ∃ x ∈ domain, cache.NewTail final.2 (pinnedOutputTail (p.forward x))) ?_).trans chance
    intro final reached malfunction
    by_contra no
    obtain ⟨x, requested, moved⟩ := malfunction
    apply moved
    exact generated_rows_preserve_domain cache slot valid position first message digest nonce room
      p domain (isolated nonce) safe old final reached no x requested
  · rw [ite_eq_right safe, prEvent_pure]
    simp [BiPermutation.programRows]

theorem full_domain_fresh_budget (sites : Nat) (small : sites ≤ 2^24) :
    (2:ℝ)^1024 * ((sites:ℝ)/2^1343) ≤ 1/2^295 := by
  have bound : (sites:ℝ) ≤ 2^24 := by exact_mod_cast small
  calc
    (2:ℝ)^1024 * ((sites:ℝ)/2^1343) ≤ (2:ℝ)^1024 * (2^24/2^1343) := by gcongr
    _ = _ := by norm_num

end TwoPermutationPrototype.Sampling.Quartet
