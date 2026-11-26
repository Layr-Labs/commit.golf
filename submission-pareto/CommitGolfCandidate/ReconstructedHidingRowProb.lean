import CommitGolfCandidate.ReconstructedHidingRows

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048
noncomputable local instance rowSampler {I : Type} [Fintype I] : SampleableType (I → Salt) :=
  by classical exact SampleableType.ofFintype _

section Conditional
variable {I : Type} [Fintype I] {base : Cache} {count : Nat} (state : PinnedOpenedState base count)
    (pos : I → Position) (first : Bool → I → Reply) (msg : Bool → I → TwoPermutationPrototype.Words 32)
    (digest : I → BitVec 256)

noncomputable def pairedRows (s : I → Salt) : ProbComp (List Row × List Row) := do
  let nonce := fun i => (s i).setWidth 128
  let l ← pinnedRowsNonce state pos (first false) (msg false) digest nonce
  let r ← pinnedRowsNonce state pos (first true) (msg true) digest nonce
  pure (l,r)

noncomputable def pairedSample := ($ᵗ (I → Salt)) >>= pairedRows state pos first msg digest

theorem paired_safe_charge (valid : state.high.Valid count)
    (enough : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (s : I → Salt) (x y : Reply) (off : ¬(tagHit pos x s ∨
      ∃ a, reverseUpper state.high (outputTail y) = some a ∧ tagHit pos a s)) :
    Pr{let r ← pairedRows state pos first msg digest s}[rowHits (r.1++r.2) (x,y) = true]
      ≤ 2*(Fintype.card I : ENNReal)/2^1343 := by
  classical
  let nonce := fun i => (s i).setWidth 128
  have per (w : Bool) : Pr{let rows ← pinnedRowsNonce state pos (first w) (msg w) digest nonce}[
      rowHits rows (x,y) = true] ≤ (Fintype.card I : ENNReal)/2^1343 := by
    apply rows_nonce_fresh_hit_le state valid pos (first w) (msg w) digest enough (x,y) nonce
    rintro (⟨i,hit⟩|old)
    · change pinnedPrivateSecond (pos i) (first w i) (msg w i) (nonce i) = x at hit
      exact off (Or.inl ((congrArg (fun a => tagHit pos a s) hit).mp (pinned_tag_hit pos i (first w i) (msg w i) s)))
    · exact off (Or.inr (latent_output_guess state.high valid pos (first w) (msg w) digest s y old))
  let draw := fun w => pinnedRowsNonce state pos (first w) (msg w) digest nonce
  have add := prEvent_bind_le_prEvent_add_of_support (draw false)
    (fun l => (fun r => (l,r)) <$> draw true) (fun l => rowHits l (x,y) = true)
    (fun z => rowHits (z.1++z.2) (x,y) = true) (by
      intro l _ clean
      simp only [prEvent_map]
      have notHit : rowHits l (x,y) = false := Bool.eq_false_iff.mpr clean
      simp only [rowHits] at notHit
      simpa only [rowHits,List.any_append,notHit,Bool.false_or] using per true)
  have bound := add.trans (add_le_add (per false) le_rfl)
  have twice : (Fintype.card I : ENNReal)/2^1343 + (Fintype.card I : ENNReal)/2^1343 =
      2*(Fintype.card I : ENNReal)/2^1343 := by simp only [div_eq_mul_inv]; ring
  rw [twice] at bound
  simpa only [pairedRows,draw,nonce,map_eq_bind_pure_comp,bind_assoc,Function.comp_def,pure_bind] using bound

theorem paired_charge (valid : state.high.Valid count)
    (enough : state.high.zero.entries.length + Fintype.card I ≤ 2^121) (x y : Reply) :
    Pr{let r ← pairedSample state pos first msg digest}[rowHits (r.1++r.2) (x,y) = true] ≤
      Pr{let s ← $ᵗ (I → Salt)}[tagHit pos x s ∨
        ∃ a, reverseUpper state.high (outputTail y) = some a ∧ tagHit pos a s] +
      2*(Fintype.card I : ENNReal)/2^1343 :=
  prEvent_bind_le_prEvent_add_of_support ($ᵗ (I → Salt)) (pairedRows state pos first msg digest) _ _
    (fun s _ off => paired_safe_charge state pos first msg digest valid enough s x y off)

end Conditional

theorem cache_tail_matches {base : Cache} {count : Nat} (cache : PinnedHighCache base) (valid : cache.Valid count)
    (low : PinnedLowTape) (x y : Reply) (old : (x,y) ∈ (cache.realize low).entries) :
    reverseUpper cache (outputTail y) = none ∨ reverseUpper cache (outputTail y) = some x := by
  classical
  change (x,y) ∈ cache.added.map (fun r => r.realize low) ++ base.entries at old
  rcases List.mem_append.mp old with added|known
  · obtain ⟨r,present,eq⟩ := List.mem_map.mp added
    have top : outputTail y = r.upper := by
      change pinnedOutputTail y = r.upper
      rw [←show (r.realize low).2=y from congrArg Prod.snd eq]
      exact pinned_high_row_tail r low
    have source : r.input=x := congrArg Prod.fst eq
    rw [top,←source]
    exact Or.inr (reverse_upper_lookup cache valid (pinned_added_upper_read cache valid r present))
  · left
    have none : ¬∃ a, pinnedAddedUpper cache a = some (outputTail y) := by
      rintro ⟨a,h⟩
      unfold pinnedAddedUpper at h
      split at h
      · rename_i found
        have chosen := Classical.choose_spec found
        have ht := Option.some.inj h
        have disjoint := valid.chooserTail _ chosen.1
        apply disjoint
        rw [ht]
        exact List.mem_map.mpr ⟨(x,y),known,rfl⟩
      · cases h
    rw [reverseUpper,dite_eq_right none]

theorem cached_pair_charge {I : Type} [Fintype I] [DecidableEq I] {base : Cache} {count : Nat}
    (state : PinnedOpenedState base count) (valid : state.high.Valid count)
    (pos : I → Position) (unique : Function.Injective pos) (first : Bool → I → Reply)
    (msg : Bool → I → TwoPermutationPrototype.Words 32) (digest : I → BitVec 256)
    (enough : state.high.zero.entries.length + Fintype.card I ≤ 2^121)
    (low : PinnedLowTape) (x y : Reply) (known : (x,y) ∈ (state.high.realize low).entries) :
    Pr{let r ← pairedSample state pos first msg digest}[rowHits (r.1++r.2) (x,y) = true] ≤
      1/2^120 + 2*(Fintype.card I : ENNReal)/2^1343 := by
  refine (paired_charge state pos first msg digest valid enough x y).trans (add_le_add ?_ le_rfl)
  refine (prEvent_mono _ _ (tagHit pos x) ?_).trans (tag_hit_le pos unique x)
  rintro s (h|⟨a,found,hit⟩)
  · exact h
  · rcases cache_tail_matches state.high valid low x y known with absent|recorded
    · rw [absent] at found; cases found
    · exact (Option.some.inj (found.symm.trans recorded)) ▸ hit

end CommitGolfCandidate.Reconstruction.HidingTape
