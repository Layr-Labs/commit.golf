import CommitGolfCandidate.MidHidingEvents

/-! One call names the unopened leaves it can hit.

The row of an unopened leaf holds its pair's midpoint and a private 128-bit
half that the opening never shows. A call can equal such a row only if it
carries that midpoint in the matching field. When no midpoint value is shared
by five pairs, a fixed block therefore matches at most four even and four odd
unopened leaves, and each match needs one fixed value of an independent
uniform half. This gives `8 / 2^128` per call, for any opening size.

Follows dadon's b4f31491 (`MoonHiding`, `single_query_hit_given_good_sM` and
`trace_hit_given_good_sM`). -/
namespace CommitGolfCandidate.LateHiding

-- Observations retain the discrete measurable structure used by the contract.
local instance observerDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec

/-- With the revealed parts fixed and no midpoint shared by five pairs, a fixed
block is the row of an unopened leaf with probability at most `8 / 2^128` over
the private halves. -/
theorem single_query_hit (ab : Index → Late.Digest × Late.Digest) (positions : Positions)
    (sLOpen : PairIndex → BitVec 128) (sM : PairIndex → BitVec 64) (sROpen : PairIndex → BitVec 128)
    (hgood : ¬ BadMidpoint sM) (x : Late.Block) :
    prEvent ((fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 128) =>
      ∃ i ∉ positions,
        rowOf ab (unpackTape (mergeWords positions sLOpen sM sROpen p.1 p.2)) i = x) <$>
      ($ᵗ ((PairIndex → BitVec 128) × (PairIndex → BitVec 128)))) ≤ (8 : ENNReal) / 2 ^ 128 := by
  let E : Finset PairIndex :=
    Finset.univ.filter (fun j : PairIndex => sM j = (saltField false x).extractLsb' 128 64)
  let O : Finset PairIndex :=
    Finset.univ.filter (fun j : PairIndex => sM j = (saltField true x).extractLsb' 0 64)
  have hEcard : E.card ≤ 4 := by
    by_contra h
    exact hgood ⟨(saltField false x).extractLsb' 128 64, by dsimp only [E] at h; omega⟩
  have hOcard : O.card ≤ 4 := by
    by_contra h
    exact hgood ⟨(saltField true x).extractLsb' 0 64, by dsimp only [O] at h; omega⟩
  let μ := $ᵗ ((PairIndex → BitVec 128) × (PairIndex → BitVec 128))
  have hsplit : prEvent ((fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 128) =>
      ∃ i ∉ positions,
        rowOf ab (unpackTape (mergeWords positions sLOpen sM sROpen p.1 p.2)) i = x) <$> μ) ≤
      prEvent ((fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 128) =>
        ∃ j ∈ E, p.1 j = (saltField false x).extractLsb' 0 128) <$> μ) +
      prEvent ((fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 128) =>
        ∃ j ∈ O, p.2 j = (saltField true x).extractLsb' 64 128) <$> μ) := by
    refine (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_or_le μ _ _)
    rintro ⟨sLHid, sRHid⟩ _ ⟨i, hi, heq⟩
    have same : rowOf ab (unpackTape (mergeWords positions sLOpen sM sROpen sLHid sRHid)) i = x :=
      heq
    have field := row_salt ab (unpackTape (mergeWords positions sLOpen sM sROpen sLHid sRHid)) i
    rw [same] at field
    by_cases he : i.val % 2 = 0
    · left
      rw [test_bit_even he,
        unpack_merge_hidden_even positions sLOpen sM sROpen sLHid sRHid i hi he] at field
      have h64 : sM (pairOf i) = (saltField false x).extractLsb' 128 64 := by
        rw [field, BitVec.extractLsb'_append_eq_of_le (by decide : 128 ≤ 128)]
        simp
      have h128 : sLHid (pairOf i) = (saltField false x).extractLsb' 0 128 := by
        rw [field]
        exact BitVec.extractLsb'_append_eq_right.symm
      exact ⟨pairOf i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h64⟩, h128⟩
    · right
      rw [test_bit_odd he,
        unpack_merge_hidden_odd positions sLOpen sM sROpen sLHid sRHid i hi he] at field
      have h64 : sM (pairOf i) = (saltField true x).extractLsb' 0 64 := by
        rw [field]
        exact BitVec.extractLsb'_append_eq_right.symm
      have h128 : sRHid (pairOf i) = (saltField true x).extractLsb' 64 128 := by
        rw [field, BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 64)]
        simp
      exact ⟨pairOf i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h64⟩, h128⟩
  have hFst : ∀ j : PairIndex,
      prEvent ((fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 128) =>
        p.1 j = (saltField false x).extractLsb' 0 128) <$> μ) ≤ (1 : ENNReal) / 2 ^ 128 := by
    intro j
    apply prEvent_prod_fst_le (A := PairIndex → BitVec 128) (B := PairIndex → BitVec 128)
      (fun f => f j = (saltField false x).extractLsb' 0 128)
    refine prEvent_uniform_coord_le (D := PairIndex) (R := BitVec 128) j
      (fun v => v = (saltField false x).extractLsb' 0 128) ?_
    rw [prEvent_uniform_eq_target, Fintype.card_bitVec 128]
    simp only [Nat.cast_pow, Nat.cast_ofNat, le_refl]
  have hSnd : ∀ j : PairIndex,
      prEvent ((fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 128) =>
        p.2 j = (saltField true x).extractLsb' 64 128) <$> μ) ≤ (1 : ENNReal) / 2 ^ 128 := by
    intro j
    apply prEvent_prod_snd_le (A := PairIndex → BitVec 128) (B := PairIndex → BitVec 128)
      (fun f => f j = (saltField true x).extractLsb' 64 128)
    refine prEvent_uniform_coord_le (D := PairIndex) (R := BitVec 128) j
      (fun v => v = (saltField true x).extractLsb' 64 128) ?_
    rw [prEvent_uniform_eq_target, Fintype.card_bitVec 128]
    simp only [Nat.cast_pow, Nat.cast_ofNat, le_refl]
  have hEbd : prEvent ((fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 128) =>
      ∃ j ∈ E, p.1 j = (saltField false x).extractLsb' 0 128) <$> μ) ≤ (4 : ENNReal) / 2 ^ 128 := by
    refine (prEvent_exists_finset_le_sum μ E _).trans
      ((Finset.sum_le_sum (fun j _ => hFst j)).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr hEcard) _
  have hObd : prEvent ((fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 128) =>
      ∃ j ∈ O, p.2 j = (saltField true x).extractLsb' 64 128) <$> μ) ≤ (4 : ENNReal) / 2 ^ 128 := by
    refine (prEvent_exists_finset_le_sum μ O _).trans
      ((Finset.sum_le_sum (fun j _ => hSnd j)).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    exact ENNReal.div_le_div_right (Nat.cast_le.mpr hOcard) _
  refine (hsplit.trans (add_le_add hEbd hObd)).trans ?_
  rw [← ENNReal.add_div]; norm_num

/-- A fixed list of calls hits the row of an unopened leaf with probability at
most `8 * length / 2^128` over the private halves. -/
theorem trace_hit (ab : Index → Late.Digest × Late.Digest) (positions : Positions)
    (sLOpen : PairIndex → BitVec 128) (sM : PairIndex → BitVec 64) (sROpen : PairIndex → BitVec 128)
    (hgood : ¬ BadMidpoint sM) (tr : List Late.Block) :
    prEvent ((fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 128) =>
      tr.any (fun x => decide (∃ i ∉ positions,
        rowOf ab (unpackTape (mergeWords positions sLOpen sM sROpen p.1 p.2)) i = x)) = true) <$>
      ($ᵗ ((PairIndex → BitVec 128) × (PairIndex → BitVec 128)))) ≤
      ((8 * tr.length : Nat) : ENNReal) / 2 ^ 128 := by
  induction tr with
  | nil =>
    have hz : prEvent ((fun _ : (PairIndex → BitVec 128) × (PairIndex → BitVec 128) =>
        false = true) <$> ($ᵗ ((PairIndex → BitVec 128) × (PairIndex → BitVec 128)))) = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ (fun _ _ h => Bool.false_ne_true h)
    simpa only [List.any_nil, List.length_nil, Nat.mul_zero, Nat.cast_zero, ENNReal.zero_div]
      using hz.le
  | cons x rest ih =>
    have hsplit : prEvent ((fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 128) =>
        (x :: rest).any (fun y => decide (∃ i ∉ positions,
          rowOf ab (unpackTape (mergeWords positions sLOpen sM sROpen p.1 p.2)) i = y)) = true) <$>
        ($ᵗ ((PairIndex → BitVec 128) × (PairIndex → BitVec 128)))) ≤
        prEvent ((fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 128) =>
          ∃ i ∉ positions,
            rowOf ab (unpackTape (mergeWords positions sLOpen sM sROpen p.1 p.2)) i = x) <$>
          ($ᵗ ((PairIndex → BitVec 128) × (PairIndex → BitVec 128)))) +
        prEvent ((fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 128) =>
          rest.any (fun y => decide (∃ i ∉ positions,
            rowOf ab (unpackTape (mergeWords positions sLOpen sM sROpen p.1 p.2)) i = y)) = true) <$>
          ($ᵗ ((PairIndex → BitVec 128) × (PairIndex → BitVec 128)))) := by
      refine (prEvent_mono_of_support _ _ _ ?_).trans (prEvent_or_le _ _ _)
      intro p _ hany
      simp only [List.any_cons, Bool.or_eq_true, decide_eq_true_eq] at hany
      exact hany
    refine (hsplit.trans (add_le_add
      (single_query_hit ab positions sLOpen sM sROpen hgood x) ih)).trans ?_
    rw [← ENNReal.add_div, List.length_cons]
    apply ENNReal.div_le_div_right
    push_cast
    exact le_of_eq (by ring)

end CommitGolfCandidate.LateHiding
