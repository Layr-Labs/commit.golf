import CommitGolfCandidate.MidHidingProgram

/-! Salt events for the one-step hiding argument.

`rowOf ab salt i` is the final compression input of leaf `i`, built from the
two content digests `ab i` and the leaf's 192-bit salt. Over uniform pair words:

* a row equals a fixed block with probability at most `2^-192` (`row_eq_fixed_le`);
* two different rows are equal with probability at most `2^-192`, also inside a
  pair, where the two salts share 64 bits (`row_collision_le`);
* `GoodRows` (no row is a cached key, all rows distinct) fails with probability
  at most `(keys * N + N^2) / 2^192` (`bad_rows_le`);
* some row lies in a fixed list with probability at most `length * N / 2^192`
  (`rows_in_list_le`);
* five pairs share one midpoint with probability at most `(N/2)^5 / 2^256`
  (`bad_midpoint_words_le`).

The collision and midpoint bounds follow dadon's b4f31491 (`MoonHiding`,
section 4: `hiddenCall3_pair_collision_le`, `badRand_t2_le`,
`badRand_pairColl_le`, `BadMidpoint`, `badMidpoint_le`). -/
namespace CommitGolfCandidate.LateHiding

-- Observations retain the discrete measurable structure used by the contract.
local instance eventsDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec

/-! ### The salt field of a final row -/

/-- Where a final row keeps its salt: the low 192 bits of an odd row, the high
192 bits of an even row. -/
def saltField (odd : Bool) (x : Late.Block) : Late.Salt :=
  x.extractLsb' (if odd then 0 else 576) 192

private theorem even_row_salt (s : Late.Salt) (a b : Late.Digest) :
    (((s ++ (0 : BitVec 64)) ++ b) ++ a).extractLsb' 576 192 = s := by
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 576)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 576 - 256)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 576 - 256 - 256)]
  simp

private theorem odd_row_salt (s : Late.Salt) (a b : Late.Digest) :
    (((b ++ a) ++ (0 : BitVec 64)) ++ s).extractLsb' 0 192 = s :=
  BitVec.extractLsb'_append_eq_right

private theorem odd_row_high (s : Late.Salt) (a b : Late.Digest) :
    (((b ++ a) ++ (0 : BitVec 64)) ++ s).extractLsb' 576 192 = b.extractLsb' 64 192 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hk, decide_true, Bool.true_and,
    show ¬ (576 + k < 192) by omega, show ¬ (576 + k - 192 < 64) by omega,
    show ¬ (576 + k - 192 - 64 < 256) by omega, ite_false,
    show 576 + k - 192 - 64 - 256 = 64 + k by omega]

private theorem even_row_low (s : Late.Salt) (a b : Late.Digest) :
    (((s ++ (0 : BitVec 64)) ++ b) ++ a).extractLsb' 0 192 = a.extractLsb' 0 192 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.zero_add,
    hk, decide_true, Bool.true_and, show k < 256 by omega, ite_true]

/-- A final row determines its salt. -/
theorem salt_field_final (odd : Bool) (s : Late.Salt) (a b : Late.Digest) :
    saltField odd (Late.finalBlock odd s a b) = s := by
  cases odd
  · exact even_row_salt s a b
  · exact odd_row_salt s a b

/-- Read as an even row, an odd row shows part of its second digest in the salt field. -/
theorem salt_field_cross_even (s : Late.Salt) (a b : Late.Digest) :
    saltField false (Late.finalBlock true s a b) = b.extractLsb' 64 192 :=
  odd_row_high s a b

/-- Read as an odd row, an even row shows part of its first digest in the salt field. -/
theorem salt_field_cross_odd (s : Late.Salt) (a b : Late.Digest) :
    saltField true (Late.finalBlock false s a b) = a.extractLsb' 0 192 :=
  even_row_low s a b

/-! ### Rows -/

/-- The final compression input of leaf `i`. -/
def rowOf (ab : Index → Late.Digest × Late.Digest) (salt : Late.SaltTape) (i : Index) : Late.Block :=
  Late.finalBlock (i.val.testBit 0) (salt i) (ab i).1 (ab i).2

theorem row_salt (ab : Index → Late.Digest × Late.Digest) (salt : Late.SaltTape) (i : Index) :
    saltField (i.val.testBit 0) (rowOf ab salt i) = salt i :=
  salt_field_final _ _ _ _

theorem pair_salt_target (odd : Bool) (t : Late.Salt) :
    prEvent ((fun r : Late.PairCoins => Late.pairSalts r odd = t) <$> ($ᵗ Late.PairCoins)) ≤
      (1 : ENNReal) / 2 ^ 192 := by
  cases odd
  · exact pair_salt_even_target t
  · exact pair_salt_odd_target t

/-- A row hits a fixed block only by hitting its 192-bit salt field. -/
theorem row_eq_fixed_le (ab : Index → Late.Digest × Late.Digest) (i : Index) (x : Late.Block) :
    prEvent ((fun words : PairIndex → Late.PairCoins => rowOf ab (unpackTape words) i = x) <$>
      ($ᵗ (PairIndex → Late.PairCoins))) ≤ (1 : ENNReal) / 2 ^ 192 := by
  refine (prEvent_mono_of_support _ _ _ ?_).trans
    (salt_target_le i (saltField (i.val.testBit 0) x))
  intro words _ same
  rw [← same, row_salt]

/-- Two different leaves have equal rows with probability at most `2^-192`. In
one pair the two leaves have opposite parity, and an even row equals an odd row
only if its whole salt equals a fixed slice of the other leaf's digest. In
different pairs the salts are independent. -/
theorem row_collision_le (ab : Index → Late.Digest × Late.Digest) (i i' : Index) (hne : i ≠ i') :
    prEvent ((fun words : PairIndex → Late.PairCoins =>
      rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i') <$>
      ($ᵗ (PairIndex → Late.PairCoins))) ≤ (1 : ENNReal) / 2 ^ 192 := by
  by_cases hpair : pairOf i = pairOf i'
  · have hv : i.val / 2 = i'.val / 2 := congrArg Fin.val hpair
    by_cases he : i.val % 2 = 0
    · have ho' : i'.val % 2 ≠ 0 := by
        intro he'
        exact hne (Fin.ext (by omega))
      refine (prEvent_mono_of_support _ _ _ ?_).trans
        (salt_target_le i ((ab i').2.extractLsb' 64 192))
      intro words _ heq
      have hc := congrArg (saltField false) heq
      have left : saltField false (rowOf ab (unpackTape words) i) = unpackTape words i := by
        unfold rowOf
        rw [test_bit_even he]
        exact salt_field_final false _ _ _
      have right : saltField false (rowOf ab (unpackTape words) i') =
          (ab i').2.extractLsb' 64 192 := by
        unfold rowOf
        rw [test_bit_odd ho']
        exact salt_field_cross_even _ _ _
      exact left.symm.trans (hc.trans right)
    · have he' : i'.val % 2 = 0 := by
        by_contra ho'
        exact hne (Fin.ext (by omega))
      refine (prEvent_mono_of_support _ _ _ ?_).trans
        (salt_target_le i ((ab i').1.extractLsb' 0 192))
      intro words _ heq
      have hc := congrArg (saltField true) heq
      have left : saltField true (rowOf ab (unpackTape words) i) = unpackTape words i := by
        unfold rowOf
        rw [test_bit_odd he]
        exact salt_field_final true _ _ _
      have right : saltField true (rowOf ab (unpackTape words) i') =
          (ab i').1.extractLsb' 0 192 := by
        unfold rowOf
        rw [test_bit_even he']
        exact salt_field_cross_odd _ _ _
      exact left.symm.trans (hc.trans right)
  · apply prEvent_uniform_coord_cond_le (D := PairIndex) (R := Late.PairCoins) (pairOf i)
    intro words
    have hfixed : ∀ r : Late.PairCoins,
        rowOf ab (unpackTape (Function.update words (pairOf i) r)) i' =
          rowOf ab (unpackTape words) i' := by
      intro r
      have hs : unpackTape (Function.update words (pairOf i) r) i' = unpackTape words i' := by
        change Late.pairSalts (Function.update words (pairOf i) r (pairOf i')) _ =
          Late.pairSalts (words (pairOf i')) _
        rw [Function.update_of_ne (Ne.symm hpair)]
      unfold rowOf
      rw [hs]
    simp only [hfixed]
    refine (prEvent_mono_of_support _ _ _ ?_).trans
      (pair_salt_target (i.val.testBit 0)
        (saltField (i.val.testBit 0) (rowOf ab (unpackTape words) i')))
    intro r _ heq
    have hc := congrArg (saltField (i.val.testBit 0)) heq
    rw [row_salt] at hc
    have hs : unpackTape (Function.update words (pairOf i) r) i =
        Late.pairSalts r (i.val.testBit 0) := by
      change Late.pairSalts (Function.update words (pairOf i) r (pairOf i)) _ = _
      rw [Function.update_self]
    exact hs.symm.trans hc

/-- No row is a key the cache already holds, except with `keys * N / 2^192`. -/
theorem rows_cached_le (cache : CompressionCache) (keys : Finset Late.Block)
    (covered : ∀ k, cache k ≠ none → k ∈ keys) (ab : Index → Late.Digest × Late.Digest) :
    prEvent ((fun words : PairIndex → Late.PairCoins =>
      ∃ i : Index, cache (rowOf ab (unpackTape words) i) ≠ none) <$>
      ($ᵗ (PairIndex → Late.PairCoins))) ≤
      ((keys.card * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
  let S2 : Finset (Late.Block × Index) := keys ×ˢ (Finset.univ : Finset Index)
  have hle : prEvent ((fun words : PairIndex → Late.PairCoins =>
        ∃ i : Index, cache (rowOf ab (unpackTape words) i) ≠ none) <$>
        ($ᵗ (PairIndex → Late.PairCoins))) ≤
      prEvent ((fun words : PairIndex → Late.PairCoins => ∃ p ∈ S2,
        rowOf ab (unpackTape words) p.2 = p.1) <$> ($ᵗ (PairIndex → Late.PairCoins))) := by
    apply prEvent_mono_of_support
    intro words _ ⟨i, hne⟩
    exact ⟨(rowOf ab (unpackTape words) i, i),
      Finset.mem_product.mpr ⟨covered _ hne, Finset.mem_univ i⟩, rfl⟩
  have hsum : prEvent ((fun words : PairIndex → Late.PairCoins => ∃ p ∈ S2,
        rowOf ab (unpackTape words) p.2 = p.1) <$> ($ᵗ (PairIndex → Late.PairCoins))) ≤
      ∑ p ∈ S2, prEvent ((fun words : PairIndex → Late.PairCoins =>
        rowOf ab (unpackTape words) p.2 = p.1) <$> ($ᵗ (PairIndex → Late.PairCoins))) :=
    prEvent_exists_finset_le_sum ($ᵗ (PairIndex → Late.PairCoins)) S2
      (fun p words => rowOf ab (unpackTape words) p.2 = p.1)
  have hbd : ∑ p ∈ S2, prEvent ((fun words : PairIndex → Late.PairCoins =>
        rowOf ab (unpackTape words) p.2 = p.1) <$> ($ᵗ (PairIndex → Late.PairCoins))) ≤
      ∑ _p ∈ S2, ((1 : ENNReal) / 2 ^ 192) :=
    Finset.sum_le_sum (fun p _ => row_eq_fixed_le ab p.2 p.1)
  refine hle.trans (hsum.trans (hbd.trans ?_))
  rw [Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one_div]

/-- All rows are pairwise distinct, except with `N^2 / 2^192`. -/
theorem rows_collide_le (ab : Index → Late.Digest × Late.Digest) :
    prEvent ((fun words : PairIndex → Late.PairCoins => ∃ i : Index, ∃ i' : Index, i ≠ i' ∧
      rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i') <$>
      ($ᵗ (PairIndex → Late.PairCoins))) ≤
      ((LENGTH * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
  have houter : prEvent ((fun words : PairIndex → Late.PairCoins => ∃ i : Index, ∃ i' : Index,
        i ≠ i' ∧ rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i') <$>
        ($ᵗ (PairIndex → Late.PairCoins))) ≤
      ∑ i : Index, prEvent ((fun words : PairIndex → Late.PairCoins => ∃ i' : Index, i ≠ i' ∧
        rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i') <$>
        ($ᵗ (PairIndex → Late.PairCoins))) :=
    prEvent_exists_le_sum (ι := Index) ($ᵗ (PairIndex → Late.PairCoins))
      (fun i words => ∃ i' : Index, i ≠ i' ∧
        rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i')
  have hrow : ∀ i : Index, prEvent ((fun words : PairIndex → Late.PairCoins => ∃ i' : Index,
      i ≠ i' ∧ rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i') <$>
      ($ᵗ (PairIndex → Late.PairCoins))) ≤ (LENGTH : ENNReal) / 2 ^ 192 := by
    intro i
    have hinner : prEvent ((fun words : PairIndex → Late.PairCoins => ∃ i' : Index, i ≠ i' ∧
          rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i') <$>
          ($ᵗ (PairIndex → Late.PairCoins))) ≤
        ∑ i' : Index, prEvent ((fun words : PairIndex → Late.PairCoins => i ≠ i' ∧
          rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i') <$>
          ($ᵗ (PairIndex → Late.PairCoins))) :=
      prEvent_exists_le_sum (ι := Index) ($ᵗ (PairIndex → Late.PairCoins))
        (fun i' words => i ≠ i' ∧
          rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i')
    have hterm : ∀ i' : Index, prEvent ((fun words : PairIndex → Late.PairCoins => i ≠ i' ∧
        rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i') <$>
        ($ᵗ (PairIndex → Late.PairCoins))) ≤ (1 : ENNReal) / 2 ^ 192 := by
      intro i'
      by_cases hne : i ≠ i'
      · exact (prEvent_mono_of_support ($ᵗ (PairIndex → Late.PairCoins))
          (fun words => i ≠ i' ∧ rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i')
          (fun words => rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i')
          (fun _ _ h => h.2)).trans (row_collision_le ab i i' hne)
      · have hz : prEvent ((fun words : PairIndex → Late.PairCoins => i ≠ i' ∧
            rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i') <$>
            ($ᵗ (PairIndex → Late.PairCoins))) = 0 :=
          prEvent_eq_zero_of_forall_mem_support ($ᵗ (PairIndex → Late.PairCoins))
            (fun words => i ≠ i' ∧
              rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i')
            (fun _ _ h => hne h.1)
        exact (le_of_eq hz).trans zero_le
    have hbd : ∑ i' : Index, prEvent ((fun words : PairIndex → Late.PairCoins => i ≠ i' ∧
          rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i') <$>
          ($ᵗ (PairIndex → Late.PairCoins))) ≤
        ∑ _i' : Index, ((1 : ENNReal) / 2 ^ 192) :=
      Finset.sum_le_sum (fun i' _ => hterm i')
    refine hinner.trans (hbd.trans ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]
  have hbd2 : ∑ i : Index, prEvent ((fun words : PairIndex → Late.PairCoins => ∃ i' : Index,
        i ≠ i' ∧ rowOf ab (unpackTape words) i = rowOf ab (unpackTape words) i') <$>
        ($ᵗ (PairIndex → Late.PairCoins))) ≤
      ∑ _i : Index, ((LENGTH : ENNReal) / 2 ^ 192) :=
    Finset.sum_le_sum (fun i _ => hrow i)
  refine houter.trans (hbd2.trans ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv,
    div_eq_mul_inv, ← mul_assoc, ← Nat.cast_mul]

/-- The rows the programming step needs: none is a cached key and no two are equal. -/
def GoodRows (cache : CompressionCache) (ab : Index → Late.Digest × Late.Digest)
    (words : PairIndex → Late.PairCoins) : Prop :=
  (∀ i : Index, cache (rowOf ab (unpackTape words) i) = none) ∧
    Function.Injective (rowOf ab (unpackTape words))

theorem bad_rows_le (cache : CompressionCache) (keys : Finset Late.Block)
    (covered : ∀ k, cache k ≠ none → k ∈ keys) (ab : Index → Late.Digest × Late.Digest) :
    prEvent ((fun words : PairIndex → Late.PairCoins => ¬ GoodRows cache ab words) <$>
      ($ᵗ (PairIndex → Late.PairCoins))) ≤
      ((keys.card * LENGTH + LENGTH * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
  have cached := rows_cached_le cache keys covered ab
  have collide := rows_collide_le ab
  refine (prEvent_mono_of_support _ _ _ ?_).trans
    ((prEvent_or_le ($ᵗ (PairIndex → Late.PairCoins)) _ _).trans
      ((add_le_add cached collide).trans ?_))
  · intro words _ bad
    by_cases populated : ∃ i : Index, cache (rowOf ab (unpackTape words) i) ≠ none
    · exact Or.inl populated
    · right
      by_contra distinct
      apply bad
      refine ⟨fun i => ?_, fun i i' same => ?_⟩
      · by_contra full
        exact populated ⟨i, full⟩
      · by_contra different
        exact distinct ⟨i, i', different, same⟩
  · rw [← ENNReal.add_div, ← Nat.cast_add]

/-- A fixed list of blocks contains some row with probability at most
`length * N / 2^192`. The list must not depend on the salts. -/
theorem rows_in_list_le (ab : Index → Late.Digest × Late.Digest) (blocks : List Late.Block) :
    prEvent ((fun words : PairIndex → Late.PairCoins =>
      ∃ i : Index, rowOf ab (unpackTape words) i ∈ blocks) <$>
      ($ᵗ (PairIndex → Late.PairCoins))) ≤
      ((blocks.length * LENGTH : Nat) : ENNReal) / 2 ^ 192 := by
  classical
  let S2 : Finset (Late.Block × Index) := blocks.toFinset ×ˢ (Finset.univ : Finset Index)
  have hle : prEvent ((fun words : PairIndex → Late.PairCoins =>
        ∃ i : Index, rowOf ab (unpackTape words) i ∈ blocks) <$>
        ($ᵗ (PairIndex → Late.PairCoins))) ≤
      prEvent ((fun words : PairIndex → Late.PairCoins => ∃ p ∈ S2,
        rowOf ab (unpackTape words) p.2 = p.1) <$> ($ᵗ (PairIndex → Late.PairCoins))) := by
    apply prEvent_mono_of_support
    intro words _ ⟨i, member⟩
    exact ⟨(rowOf ab (unpackTape words) i, i),
      Finset.mem_product.mpr ⟨List.mem_toFinset.mpr member, Finset.mem_univ i⟩, rfl⟩
  have hsum : prEvent ((fun words : PairIndex → Late.PairCoins => ∃ p ∈ S2,
        rowOf ab (unpackTape words) p.2 = p.1) <$> ($ᵗ (PairIndex → Late.PairCoins))) ≤
      ∑ p ∈ S2, prEvent ((fun words : PairIndex → Late.PairCoins =>
        rowOf ab (unpackTape words) p.2 = p.1) <$> ($ᵗ (PairIndex → Late.PairCoins))) :=
    prEvent_exists_finset_le_sum ($ᵗ (PairIndex → Late.PairCoins)) S2
      (fun p words => rowOf ab (unpackTape words) p.2 = p.1)
  have hbd : ∑ p ∈ S2, prEvent ((fun words : PairIndex → Late.PairCoins =>
        rowOf ab (unpackTape words) p.2 = p.1) <$> ($ᵗ (PairIndex → Late.PairCoins))) ≤
      ∑ _p ∈ S2, ((1 : ENNReal) / 2 ^ 192) :=
    Finset.sum_le_sum (fun p _ => row_eq_fixed_le ab p.2 p.1)
  refine hle.trans (hsum.trans (hbd.trans ?_))
  rw [Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one_div]
  apply ENNReal.div_le_div_right
  exact Nat.cast_le.mpr (Nat.mul_le_mul_right LENGTH (List.toFinset_card_le blocks))

/-! ### Midpoints shared by five pairs -/

/-- Midpoint bad event: some 64-bit value appears in 5 or more pairs of `sM`. -/
def BadMidpoint (sM : PairIndex → BitVec 64) : Prop :=
  ∃ m : BitVec 64, 5 ≤ (Finset.univ.filter (fun j : PairIndex => sM j = m)).card

theorem five_distinct_of_card_ge_five {α : Type} [DecidableEq α] {S : Finset α}
    (h : 5 ≤ S.card) :
    ∃ a0 a1 a2 a3 a4 : α, a0 ∈ S ∧ a1 ∈ S ∧ a2 ∈ S ∧ a3 ∈ S ∧ a4 ∈ S ∧
      a0 ≠ a1 ∧ a0 ≠ a2 ∧ a0 ≠ a3 ∧ a0 ≠ a4 ∧
      a1 ≠ a2 ∧ a1 ≠ a3 ∧ a1 ≠ a4 ∧
      a2 ≠ a3 ∧ a2 ≠ a4 ∧ a3 ≠ a4 := by
  have h0 : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a0, ha0⟩ := h0
  let S1 := S.erase a0
  have hc1 : 4 ≤ S1.card := by dsimp only [S1]; rw [Finset.card_erase_of_mem ha0]; omega
  obtain ⟨a1, ha1⟩ := Finset.card_pos.mp (by omega : 0 < S1.card)
  let S2 := S1.erase a1
  have hc2 : 3 ≤ S2.card := by dsimp only [S2]; rw [Finset.card_erase_of_mem ha1]; omega
  obtain ⟨a2, ha2⟩ := Finset.card_pos.mp (by omega : 0 < S2.card)
  let S3 := S2.erase a2
  have hc3 : 2 ≤ S3.card := by dsimp only [S3]; rw [Finset.card_erase_of_mem ha2]; omega
  obtain ⟨a3, ha3⟩ := Finset.card_pos.mp (by omega : 0 < S3.card)
  let S4 := S3.erase a3
  have hc4 : 1 ≤ S4.card := by dsimp only [S4]; rw [Finset.card_erase_of_mem ha3]; omega
  obtain ⟨a4, ha4⟩ := Finset.card_pos.mp (by omega : 0 < S4.card)
  have m1 := Finset.mem_erase.mp ha1
  have m2 := Finset.mem_erase.mp ha2
  have m2' := Finset.mem_erase.mp m2.2
  have m3 := Finset.mem_erase.mp ha3
  have m3' := Finset.mem_erase.mp m3.2
  have m3'' := Finset.mem_erase.mp m3'.2
  have m4 := Finset.mem_erase.mp ha4
  have m4' := Finset.mem_erase.mp m4.2
  have m4'' := Finset.mem_erase.mp m4'.2
  have m4''' := Finset.mem_erase.mp m4''.2
  exact ⟨a0, a1, a2, a3, a4, ha0, m1.2, m2'.2, m3''.2, m4'''.2,
    Ne.symm m1.1, Ne.symm m2'.1, Ne.symm m3''.1, Ne.symm m4'''.1,
    Ne.symm m2.1, Ne.symm m3'.1, Ne.symm m4''.1,
    Ne.symm m3.1, Ne.symm m4'.1, Ne.symm m4.1⟩


theorem prEvent_uniform_bv64_eq_and (t : BitVec 64) (q : ProbComp Prop) {r : ENNReal}
    (hq : prEvent (id <$> q) ≤ r) :
    prEvent (id <$> (do let v ← $ᵗ BitVec 64; let p ← q; pure (v = t ∧ p))) ≤
      ((1 : ENNReal) / 2 ^ 64) * r := by
  rw [prEvent_bind_eq_sum_fintype]
  have hterm : ∀ v : BitVec 64,
      Pr{let x ← $ᵗ BitVec 64}[x = v] *
        prEvent (id <$> (do let p ← q; pure (v = t ∧ p))) ≤
      (if v = t then ((1 : ENNReal) / 2 ^ 64) * r else 0) := by
    intro v
    by_cases hv : v = t
    · subst hv
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      have hv1 : Pr{let x ← $ᵗ BitVec 64}[x = v] = (1 : ENNReal) / 2 ^ 64 := by
        have h := prEvent_uniform_eq_target (α := BitVec 64) v
        rw [Fintype.card_bitVec 64, Nat.cast_pow, Nat.cast_ofNat] at h
        exact h
      have hq' : prEvent (id <$> (do let p ← q; pure (v = v ∧ p))) ≤ r := by
        have heq : (do let p ← q; pure (v = v ∧ p)) = q := by
          rw [show (fun p : Prop => (pure (v = v ∧ p) : ProbComp Prop)) = pure from
            funext (fun p => congrArg pure (propext ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩)), bind_pure]
        rw [heq]; exact hq
      rw [hv1]
      exact mul_le_mul_of_nonneg_left hq' zero_le
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
      have hz : prEvent (id <$> (do let p ← q; pure (v = t ∧ p))) ≤ 0 := by
        apply prEvent_bind_le_of_forall_le; intro p
        rw [map_pure]
        exact (prEvent_pure_mono (Q := False) (fun h => hv h.1)).trans
          (le_of_eq (by rw [prEvent_pure_prop, ite_eq_right_of_eq_false _ _ (eq_false not_false)]))
      exact (mul_le_mul_of_nonneg_left hz zero_le).trans (le_of_eq (mul_zero _))
  refine (Finset.sum_le_sum (fun v _ => hterm v)).trans ?_
  rw [Finset.sum_eq_single t
    (fun v _ hne => ite_eq_right_of_eq_false _ _ (eq_false hne))
    (fun h => (h (Finset.mem_univ t)).elim),
    ite_eq_left_of_eq_true _ _ (eq_true rfl)]


theorem four_eq_64_le {D : Type} [DecidableEq D] [Finite D]
    [SampleableType (D → BitVec 64)] (j0 j1 j2 j3 j4 : D)
    (h01 : j0 ≠ j1) (h02 : j0 ≠ j2) (h03 : j0 ≠ j3) (h04 : j0 ≠ j4)
    (h12 : j1 ≠ j2) (h13 : j1 ≠ j3) (h14 : j1 ≠ j4)
    (h23 : j2 ≠ j3) (h24 : j2 ≠ j4) (h34 : j3 ≠ j4) :
    prEvent ((fun sM : D → BitVec 64 =>
      sM j1 = sM j0 ∧ sM j2 = sM j0 ∧ sM j3 = sM j0 ∧ sM j4 = sM j0) <$>
      ($ᵗ (D → BitVec 64))) ≤ (1 : ENNReal) / 2 ^ 256 := by
  let P (f : D → BitVec 64) : Prop :=
    f j1 = f j0 ∧ f j2 = f j0 ∧ f j3 = f j0 ∧ f j4 = f j0
  let c0 : ProbComp Prop := ($ᵗ (D → BitVec 64)) >>= fun f => pure (P f)
  let c1 : ProbComp Prop := ($ᵗ (D → BitVec 64)) >>= fun f => ($ᵗ BitVec 64) >>= fun v1 =>
    pure (P (Function.update f j1 v1))
  let c2 : ProbComp Prop := ($ᵗ (D → BitVec 64)) >>= fun f => ($ᵗ BitVec 64) >>= fun v2 =>
    ($ᵗ BitVec 64) >>= fun v1 => pure (P (Function.update (Function.update f j2 v2) j1 v1))
  let c3 : ProbComp Prop := ($ᵗ (D → BitVec 64)) >>= fun f => ($ᵗ BitVec 64) >>= fun v3 =>
    ($ᵗ BitVec 64) >>= fun v2 => ($ᵗ BitVec 64) >>= fun v1 =>
    pure (P (Function.update (Function.update (Function.update f j3 v3) j2 v2) j1 v1))
  let c4 : ProbComp Prop := ($ᵗ (D → BitVec 64)) >>= fun f => ($ᵗ BitVec 64) >>= fun v4 =>
    ($ᵗ BitVec 64) >>= fun v3 => ($ᵗ BitVec 64) >>= fun v2 => ($ᵗ BitVec 64) >>= fun v1 =>
    pure (P (Function.update (Function.update (Function.update (Function.update f j4 v4) j3 v3) j2 v2) j1 v1))
  let q0 : ProbComp Prop := pure True
  let q1 (t : BitVec 64) : ProbComp Prop := ($ᵗ BitVec 64) >>= fun v1 => q0 >>= fun p0 => pure (v1 = t ∧ p0)
  let q2 (t : BitVec 64) : ProbComp Prop := ($ᵗ BitVec 64) >>= fun v2 => q1 t >>= fun p1 => pure (v2 = t ∧ p1)
  let q3 (t : BitVec 64) : ProbComp Prop := ($ᵗ BitVec 64) >>= fun v3 => q2 t >>= fun p2 => pure (v3 = t ∧ p2)
  let q4 (t : BitVec 64) : ProbComp Prop := ($ᵗ BitVec 64) >>= fun v4 => q3 t >>= fun p3 => pure (v4 = t ∧ p3)
  let c5 : ProbComp Prop := ($ᵗ (D → BitVec 64)) >>= fun f => q4 (f j0)
  rw [prEvent_map_eq_id_bind]
  change prEvent (id <$> c0) ≤ _
  have h1 : 𝒟[c0] = 𝒟[c1] :=
    (uniform_coordinate_bind (D := D) (R := BitVec 64) j1 (fun f => pure (P f))).symm
  have h2 : 𝒟[c1] = 𝒟[c2] :=
    (uniform_coordinate_bind (D := D) (R := BitVec 64) j2 (fun f =>
      ($ᵗ BitVec 64) >>= fun v1 => pure (P (Function.update f j1 v1)))).symm
  have h3 : 𝒟[c2] = 𝒟[c3] :=
    (uniform_coordinate_bind (D := D) (R := BitVec 64) j3 (fun f =>
      ($ᵗ BitVec 64) >>= fun v2 => ($ᵗ BitVec 64) >>= fun v1 =>
        pure (P (Function.update (Function.update f j2 v2) j1 v1)))).symm
  have h4 : 𝒟[c3] = 𝒟[c4] :=
    (uniform_coordinate_bind (D := D) (R := BitVec 64) j4 (fun f =>
      ($ᵗ BitVec 64) >>= fun v3 => ($ᵗ BitVec 64) >>= fun v2 => ($ᵗ BitVec 64) >>= fun v1 =>
        pure (P (Function.update (Function.update (Function.update f j3 v3) j2 v2) j1 v1)))).symm
  have h5 : 𝒟[c4] = 𝒟[c5] := by
    dsimp only [c4, c5, q4, q3, q2, q1, q0]
    apply _root_.evalDist_bind_congr; intro f
    apply _root_.evalDist_bind_congr; intro v4
    simp only [bind_assoc, pure_bind]
    apply _root_.evalDist_bind_congr; intro v3
    apply _root_.evalDist_bind_congr; intro v2
    apply _root_.evalDist_bind_congr; intro v1
    simp only [P, Function.update_self, Function.update_of_ne h01, Function.update_of_ne h02,
      Function.update_of_ne h03, Function.update_of_ne h04,
      Function.update_of_ne (Ne.symm h12), Function.update_of_ne (Ne.symm h13),
      Function.update_of_ne (Ne.symm h14), Function.update_of_ne (Ne.symm h23),
      Function.update_of_ne (Ne.symm h24), Function.update_of_ne (Ne.symm h34)]
    exact congrArg (fun q : Prop => 𝒟[(pure q : ProbComp Prop)])
      (propext ⟨fun ⟨a, b, c, d⟩ => ⟨d, c, b, a, trivial⟩, fun ⟨d, c, b, a, _⟩ => ⟨a, b, c, d⟩⟩)
  have hchain := h1.trans (h2.trans (h3.trans (h4.trans h5)))
  rw [(EvalDistEq.of_evalDist_eq hchain).prEvent_eq id]
  apply prEvent_bind_le_of_forall_le; intro f
  have h0 : prEvent (id <$> q0) ≤ 1 := by
    dsimp only [q0]
    rw [map_pure]
    change prEvent (pure True) ≤ 1
    rw [prEvent_pure_prop, ite_eq_left_of_eq_true _ _ (eq_true trivial)]
  have b1 := prEvent_uniform_bv64_eq_and (f j0) q0 h0
  have b2 := prEvent_uniform_bv64_eq_and (f j0) (q1 (f j0)) b1
  have b3 := prEvent_uniform_bv64_eq_and (f j0) (q2 (f j0)) b2
  have b4 := prEvent_uniform_bv64_eq_and (f j0) (q3 (f j0)) b3
  have hpow : ∀ a b : Nat, ((1 : ENNReal) / 2 ^ a) * ((1 : ENNReal) / 2 ^ b) = (1 : ENNReal) / 2 ^ (a + b) := fun a b => by
    rw [one_div, one_div, one_div, ← ENNReal.mul_inv (Or.inl (pow_ne_zero a two_ne_zero))
      (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), pow_add]
  refine b4.trans (le_of_eq ?_)
  rw [mul_one, hpow 64 64, hpow 64 (64 + 64), hpow 64 (64 + (64 + 64))]


theorem badMidpoint_le :
    prEvent ((fun sM : PairIndex → BitVec 64 => BadMidpoint sM) <$> ($ᵗ (PairIndex → BitVec 64))) ≤
      (((LENGTH / 2) ^ 5 : Nat) : ENNReal) / 2 ^ 256 := by
  let Tuple5 := PairIndex × PairIndex × PairIndex × PairIndex × PairIndex
  let distinct5 (q : Tuple5) : Prop :=
    let (j0, j1, j2, j3, j4) := q
    j0 ≠ j1 ∧ j0 ≠ j2 ∧ j0 ≠ j3 ∧ j0 ≠ j4 ∧
    j1 ≠ j2 ∧ j1 ≠ j3 ∧ j1 ≠ j4 ∧
    j2 ≠ j3 ∧ j2 ≠ j4 ∧ j3 ≠ j4
  let hit5 (q : Tuple5) (sM : PairIndex → BitVec 64) : Prop :=
    let (j0, j1, j2, j3, j4) := q
    distinct5 q ∧ sM j1 = sM j0 ∧ sM j2 = sM j0 ∧ sM j3 = sM j0 ∧ sM j4 = sM j0
  have hmono : prEvent ((fun sM => BadMidpoint sM) <$> ($ᵗ (PairIndex → BitVec 64))) ≤
      prEvent ((fun sM => ∃ q : Tuple5, hit5 q sM) <$> ($ᵗ (PairIndex → BitVec 64))) := by
    apply prEvent_mono_of_support
    intro sM _ ⟨m, hcard⟩
    obtain ⟨j0, j1, j2, j3, j4, m0, m1, m2, m3, m4, d01, d02, d03, d04, d12, d13, d14, d23, d24, d34⟩ :=
      five_distinct_of_card_ge_five hcard
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at m0 m1 m2 m3 m4
    exact ⟨(j0, j1, j2, j3, j4), ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34⟩,
      m1.trans m0.symm, m2.trans m0.symm, m3.trans m0.symm, m4.trans m0.symm⟩
  refine hmono.trans ((prEvent_exists_le_sum ($ᵗ (PairIndex → BitVec 64)) hit5).trans ?_)
  have hterm : ∀ q : Tuple5, prEvent ((fun sM => hit5 q sM) <$> ($ᵗ (PairIndex → BitVec 64))) ≤
      (1 : ENNReal) / 2 ^ 256 := by
    rintro ⟨j0, j1, j2, j3, j4⟩
    by_cases hd : distinct5 (j0, j1, j2, j3, j4)
    · rcases hd with ⟨d01, d02, d03, d04, d12, d13, d14, d23, d24, d34⟩
      exact (prEvent_mono_of_support _ _ _ (fun _ _ h => h.2)).trans
        (four_eq_64_le j0 j1 j2 j3 j4 d01 d02 d03 d04 d12 d13 d14 d23 d24 d34)
    · have hz : prEvent ((fun sM => hit5 (j0, j1, j2, j3, j4) sM) <$> ($ᵗ (PairIndex → BitVec 64))) = 0 :=
        prEvent_eq_zero_of_forall_mem_support _ _ (fun _ _ h => hd h.1)
      rw [hz]; exact zero_le
  refine (Finset.sum_le_sum (fun q _ => hterm q)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
  have hcard : Fintype.card Tuple5 = (LENGTH / 2) ^ 5 := by
    simp only [Tuple5, PairIndex, Fintype.card_prod, Fintype.card_fin]; ring
  rw [hcard]


theorem bad_midpoint_words_le :
    prEvent ((fun rand : PairIndex → Late.PairCoins => BadMidpoint (fun j => pairSM (rand j))) <$>
      ($ᵗ (PairIndex → Late.PairCoins))) ≤ (((LENGTH / 2) ^ 5 : Nat) : ENNReal) / 2 ^ 256 := by
  rw [prEvent_map_eq_id_bind]
  have hcb := (EvalDistEq.of_evalDist_eq
    (combine_uniform_bind (fun rand => pure (BadMidpoint (fun j => pairSM (rand j)))))).prEvent_eq id
  rw [← hcb]
  have hsimp : (do let sL ← $ᵗ (PairIndex → BitVec 128)
                   let sM ← $ᵗ (PairIndex → BitVec 64)
                   let sR ← $ᵗ (PairIndex → BitVec 128)
                   pure (BadMidpoint (fun j => pairSM (combineWords sL sM sR j)))) =
      (do let _ ← $ᵗ (PairIndex → BitVec 128)
          let sM ← $ᵗ (PairIndex → BitVec 64)
          let _ ← $ᵗ (PairIndex → BitVec 128)
          pure (BadMidpoint sM)) := by
    apply bind_congr; intro sL
    apply bind_congr; intro sM
    apply bind_congr; intro sR
    simp only [pairSM_combine]
  rw [hsimp]
  exact prEvent_bind_fst_mid_snd (A := PairIndex → BitVec 128) (B := PairIndex → BitVec 64)
    (C := PairIndex → BitVec 128) BadMidpoint badMidpoint_le


end CommitGolfCandidate.LateHiding
