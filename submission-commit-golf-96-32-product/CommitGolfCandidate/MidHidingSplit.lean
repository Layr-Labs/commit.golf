import CommitGolfCandidate.LateHidingSalts

/-! Pair words with a shared midpoint, split into independent parts.

A 320-bit pair word is `s_R ++ s_M ++ s_L` with 128, 64 and 128 bits. The even
leaf's salt is `s_M ++ s_L` and the odd leaf's salt is `s_R ++ s_M`. A uniform
function from pairs to words is three independent uniform functions, and each
of `s_L` and `s_R` splits further by an arbitrary set of pairs, here the pairs
whose even or odd leaf is opened. Each leaf's 192-bit salt is uniform on its own.

The lemmas on uniform samples and the union bounds follow dadon's b4f31491
(`MoonHidingCore`, section 1, and `MoonHiding`, section 4), restated for
`Late.pairSalts` and `unpackTape`. -/
namespace CommitGolfCandidate.LateHiding

-- Observations retain the discrete measurable structure used by the contract.
local instance splitDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec

/-! ### Pairs and parity -/

private theorem length_two : LENGTH = 2 * (LENGTH / 2) := by decide

def pairOf (i : Index) : PairIndex :=
  ⟨i.val / 2, by
    have inside := i.isLt
    have even := length_two
    omega⟩

def evenIdx (j : PairIndex) : Index :=
  ⟨2 * j.val, by
    have inside := j.isLt
    have even := length_two
    omega⟩

def oddIdx (j : PairIndex) : Index :=
  ⟨2 * j.val + 1, by
    have inside := j.isLt
    have even := length_two
    omega⟩

theorem index_eq_even (i : Index) (even : i.val % 2 = 0) : i = evenIdx (pairOf i) :=
  Fin.ext (by simp only [evenIdx, pairOf]; omega)

theorem index_eq_odd (i : Index) (odd : i.val % 2 ≠ 0) : i = oddIdx (pairOf i) :=
  Fin.ext (by simp only [oddIdx, pairOf]; omega)

theorem test_bit_even {n : Nat} (even : n % 2 = 0) : n.testBit 0 = false := by
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one, decide_eq_false_iff_not]
  omega

theorem test_bit_odd {n : Nat} (odd : n % 2 ≠ 0) : n.testBit 0 = true := by
  simp only [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one, decide_eq_true_eq]
  omega

/-! ### The three parts of a pair word -/

def pairSL (r : Late.PairCoins) : BitVec 128 := r.extractLsb' 0 128
def pairSM (r : Late.PairCoins) : BitVec 64 := r.extractLsb' 128 64
def pairSR (r : Late.PairCoins) : BitVec 128 := r.extractLsb' 192 128

theorem pair_salts_even (r : Late.PairCoins) :
    Late.pairSalts r false = pairSM r ++ pairSL r := by
  change r.extractLsb' 0 192 = _
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  unfold pairSM pairSL
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true, Bool.true_and,
    Nat.zero_add]
  by_cases h128 : b < 128
  · simp [h128]
  · have h64 : b - 128 < 64 := by omega
    simp [h128, h64, show 128 + (b - 128) = b by omega]

theorem pair_salts_odd (r : Late.PairCoins) :
    Late.pairSalts r true = pairSR r ++ pairSM r := by
  change r.extractLsb' 128 192 = _
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  unfold pairSR pairSM
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true, Bool.true_and]
  by_cases h64 : b < 64
  · simp [h64]
  · have h128 : b - 64 < 128 := by omega
    simp [h64, h128, show 192 + (b - 64) = 128 + b by omega]

theorem pair_word_parts (r : Late.PairCoins) : r = (pairSR r ++ pairSM r) ++ pairSL r := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  unfold pairSR pairSM pairSL
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', Nat.zero_add]
  by_cases h128 : b < 128
  · simp [h128]
  · by_cases h192 : b < 192
    · have h64 : b - 128 < 64 := by omega
      simp [h128, h64, show 128 + (b - 128) = b by omega]
    · have h64 : ¬ (b - 128 < 64) := by omega
      have hhi : b - 128 - 64 < 128 := by omega
      simp [h128, h64, hhi, show 192 + (b - 128 - 64) = b by omega]

/-- The salt of leaf `i`, by parity. -/
theorem unpack_even (words : PairIndex → Late.PairCoins) (i : Index) (even : i.val % 2 = 0) :
    unpackTape words i = pairSM (words (pairOf i)) ++ pairSL (words (pairOf i)) := by
  change Late.pairSalts (words (pairOf i)) (i.val.testBit 0) = _
  rw [test_bit_even even, pair_salts_even]

theorem unpack_odd (words : PairIndex → Late.PairCoins) (i : Index) (odd : i.val % 2 ≠ 0) :
    unpackTape words i = pairSR (words (pairOf i)) ++ pairSM (words (pairOf i)) := by
  change Late.pairSalts (words (pairOf i)) (i.val.testBit 0) = _
  rw [test_bit_odd odd, pair_salts_odd]

/-- The salt of leaf `i` as a window of its pair word: bits 0 to 192 for an even
leaf, bits 128 to 320 for an odd leaf. The two windows share bits 128 to 192. -/
theorem unpack_window (words : PairIndex → Late.PairCoins) (i : Index) :
    unpackTape words i =
      if i.val % 2 = 0 then (words (pairOf i)).extractLsb' 0 192
      else (words (pairOf i)).extractLsb' 128 192 := by
  by_cases even : i.val % 2 = 0
  · rw [ite_eq_left even]
    change Late.pairSalts (words (pairOf i)) (i.val.testBit 0) = _
    rw [test_bit_even even]
    rfl
  · rw [ite_eq_right even]
    change Late.pairSalts (words (pairOf i)) (i.val.testBit 0) = _
    rw [test_bit_odd even]
    rfl

def combineWords
    (sL : PairIndex → BitVec 128) (sM : PairIndex → BitVec 64) (sR : PairIndex → BitVec 128) :
    PairIndex → Late.PairCoins :=
  fun j => (sR j ++ sM j) ++ sL j

theorem pairSL_combine (sL : PairIndex → BitVec 128) (sM : PairIndex → BitVec 64)
    (sR : PairIndex → BitVec 128) (j : PairIndex) :
    pairSL (combineWords sL sM sR j) = sL j := by
  unfold pairSL combineWords
  exact BitVec.extractLsb'_append_eq_right

theorem pairSM_combine (sL : PairIndex → BitVec 128) (sM : PairIndex → BitVec 64)
    (sR : PairIndex → BitVec 128) (j : PairIndex) :
    pairSM (combineWords sL sM sR j) = sM j := by
  unfold pairSM combineWords
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 128 ≤ 128)]
  exact BitVec.extractLsb'_append_eq_right

theorem pairSR_combine (sL : PairIndex → BitVec 128) (sM : PairIndex → BitVec 64)
    (sR : PairIndex → BitVec 128) (j : PairIndex) :
    pairSR (combineWords sL sM sR j) = sR j := by
  unfold pairSR combineWords
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 128 ≤ 192)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 192 - 128)]
  simp

theorem combine_bijective :
    Function.Bijective
      (fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 64) × (PairIndex → BitVec 128) =>
        combineWords p.1 p.2.1 p.2.2) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun r => (fun j => pairSL (r j), fun j => pairSM (r j), fun j => pairSR (r j)), ?_, ?_⟩
  · rintro ⟨sL, sM, sR⟩
    refine Prod.ext (funext fun j => pairSL_combine sL sM sR j)
      (Prod.ext (funext fun j => pairSM_combine sL sM sR j)
        (funext fun j => pairSR_combine sL sM sR j))
  · intro r
    funext j
    exact (pair_word_parts (r j)).symm

/-! ### Uniform samples -/

theorem prod_uniform_bind {A B α : Type} [SampleableType A] [SampleableType B]
    (next : A × B → ProbComp α) :
    𝒟[do let a ← $ᵗ A
         let b ← $ᵗ B
         next (a, b)] =
    𝒟[($ᵗ (A × B)) >>= next] := by
  calc
    𝒟[do let a ← $ᵗ A
         let b ← $ᵗ B
         next (a, b)]
      = 𝒟[(do let a ← $ᵗ A; let b ← $ᵗ B; pure (a, b)) >>= next] := by
          simp only [bind_assoc, pure_bind]
    _ = 𝒟[($ᵗ (A × B)) >>= next] := by
          rw [← SampleableType.uniformSample_prod_eq_bind]

theorem triple_uniform_bind {A B C D α : Type}
    [SampleableType A] [SampleableType B] [SampleableType C] [SampleableType D]
    (f : A × B × C → D) (hf : Function.Bijective f) (next : D → ProbComp α) :
    𝒟[do let a ← $ᵗ A
         let b ← $ᵗ B
         let c ← $ᵗ C
         next (f (a, b, c))] =
    𝒟[($ᵗ D) >>= next] := by
  have hbij := ((SampleableType.map_uniformSample_evalDistEq_of_bijective hf).bind_left
    next).evalDist_eq
  calc
    𝒟[do let a ← $ᵗ A
         let b ← $ᵗ B
         let c ← $ᵗ C
         next (f (a, b, c))]
      = 𝒟[do let a ← $ᵗ A
             let bc ← $ᵗ (B × C)
             next (f (a, bc))] := by
          apply _root_.evalDist_bind_congr; intro a
          exact prod_uniform_bind (fun bc => next (f (a, bc)))
    _ = 𝒟[($ᵗ (A × B × C)) >>= fun p => next (f p)] :=
          prod_uniform_bind (fun p => next (f p))
    _ = 𝒟[(f <$> ($ᵗ (A × B × C))) >>= next] := by
          rw [bind_map_left]
    _ = 𝒟[($ᵗ D) >>= next] := hbij

/-- Uniform pair words are three independent uniform parts. -/
theorem combine_uniform_bind {α : Type} (next : (PairIndex → Late.PairCoins) → ProbComp α) :
    𝒟[do let sL ← $ᵗ (PairIndex → BitVec 128)
         let sM ← $ᵗ (PairIndex → BitVec 64)
         let sR ← $ᵗ (PairIndex → BitVec 128)
         next (combineWords sL sM sR)] =
    𝒟[($ᵗ (PairIndex → Late.PairCoins)) >>= next] :=
  triple_uniform_bind
    (fun p : (PairIndex → BitVec 128) × (PairIndex → BitVec 64) × (PairIndex → BitVec 128) =>
      combineWords p.1 p.2.1 p.2.2)
    combine_bijective next

/-- A uniform function is two independent uniform functions merged along any set. -/
theorem merge_function_bind {D R α : Type} [DecidableEq D]
    [SampleableType (D → R)] (S : Finset D) (next : (D → R) → ProbComp α) :
    𝒟[do let sOpen ← $ᵗ (D → R)
         let sHidden ← $ᵗ (D → R)
         next (fun i => if i ∈ S then sOpen i else sHidden i)] =
    𝒟[($ᵗ (D → R)) >>= next] := by
  let swap : (D → R) × (D → R) → (D → R) × (D → R) :=
    fun p => (fun i => if i ∈ S then p.1 i else p.2 i, fun i => if i ∈ S then p.2 i else p.1 i)
  have hinv : Function.Involutive swap := by
    rintro ⟨a, b⟩
    ext i <;> by_cases hi : i ∈ S <;> simp [swap, hi]
  have hswap := ((SampleableType.map_uniformSample_evalDistEq_of_bijective hinv.bijective).bind_left
    (fun p => next p.1)).evalDist_eq
  calc
    𝒟[do let sOpen ← $ᵗ (D → R)
         let sHidden ← $ᵗ (D → R)
         next (fun i => if i ∈ S then sOpen i else sHidden i)]
      = 𝒟[(do let sOpen ← $ᵗ (D → R)
              let sHidden ← $ᵗ (D → R)
              pure (sOpen, sHidden)) >>= fun p => next (swap p).1] := by
          simp only [bind_assoc, pure_bind, swap]
    _ = 𝒟[($ᵗ ((D → R) × (D → R))) >>= fun p => next (swap p).1] := by
          rw [← SampleableType.uniformSample_prod_eq_bind]
    _ = 𝒟[(swap <$> ($ᵗ ((D → R) × (D → R)))) >>= fun p => next p.1] := by
          rw [bind_map_left]
    _ = 𝒟[($ᵗ ((D → R) × (D → R))) >>= fun p => next p.1] := hswap
    _ = 𝒟[(do let sOpen ← $ᵗ (D → R)
              let sHidden ← $ᵗ (D → R)
              pure (sOpen, sHidden)) >>= fun p => next p.1] := by
          rw [SampleableType.uniformSample_prod_eq_bind]
    _ = 𝒟[do let sOpen ← $ᵗ (D → R)
             let _sHidden ← $ᵗ (D → R)
             next sOpen] := by
          simp only [bind_assoc, pure_bind]
    _ = 𝒟[($ᵗ (D → R)) >>= next] := by
          apply _root_.evalDist_bind_congr
          intro sOpen
          exact OracleComp.evalDist_bind_const _ _

/-- Resampling one coordinate of a uniform function preserves its distribution,
also for randomized continuations. -/
theorem uniform_coordinate_bind {D R α : Type} [DecidableEq D] [Finite D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)]
    (index : D) (next : (D → R) → ProbComp α) :
    𝒟[do let values ← $ᵗ (D → R)
         let value ← $ᵗ R
         next (Function.update values index value)] =
    𝒟[do let values ← $ᵗ (D → R); next values] := by
  have marginal : 𝒟[do let value ← $ᵗ R
                        let values ← $ᵗ (D → R)
                        pure (Function.update values index value)] = 𝒟[$ᵗ (D → R)] := by
    simpa only [bind_pure] using evalDist_uniformSample_bind_update_map
      SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample index
      (fun values : D → R => values)
  trans 𝒟[do let value ← $ᵗ R
              let values ← $ᵗ (D → R)
              next (Function.update values index value)]
  · exact distribution_bind_comm _ _ _
  · trans 𝒟[(do let value ← $ᵗ R
                let values ← $ᵗ (D → R)
                pure (Function.update values index value)) >>= next]
    · simp only [bind_assoc, pure_bind]
    · rw [evalDist_bind_of_discrete, marginal, ← evalDist_bind_of_discrete]

/-! ### Opened and hidden parts -/

def evenOpenSet (positions : Positions) : Finset PairIndex :=
  Finset.univ.filter (fun j => evenIdx j ∈ positions)

def oddOpenSet (positions : Positions) : Finset PairIndex :=
  Finset.univ.filter (fun j => oddIdx j ∈ positions)

/-- Pair words from the parts an opening reveals and the two private halves of
the unopened leaves. The midpoint `sM` counts as revealed for every pair. -/
def mergeWords (positions : Positions)
    (sLOpen : PairIndex → BitVec 128) (sM : PairIndex → BitVec 64) (sROpen : PairIndex → BitVec 128)
    (sLHid sRHid : PairIndex → BitVec 128) : PairIndex → Late.PairCoins :=
  combineWords
    (fun j => if j ∈ evenOpenSet positions then sLOpen j else sLHid j)
    sM
    (fun j => if j ∈ oddOpenSet positions then sROpen j else sRHid j)

theorem pairSM_merge (positions : Positions)
    (sLOpen : PairIndex → BitVec 128) (sM : PairIndex → BitVec 64) (sROpen : PairIndex → BitVec 128)
    (sLHid sRHid : PairIndex → BitVec 128) (j : PairIndex) :
    pairSM (mergeWords positions sLOpen sM sROpen sLHid sRHid j) = sM j :=
  pairSM_combine _ sM _ j

/-- An opened leaf's salt does not depend on the private halves. -/
theorem unpack_merge_opened (positions : Positions)
    (sLOpen : PairIndex → BitVec 128) (sM : PairIndex → BitVec 64) (sROpen : PairIndex → BitVec 128)
    (sLHid sRHid : PairIndex → BitVec 128) (i : Index) (hi : i ∈ positions) :
    unpackTape (mergeWords positions sLOpen sM sROpen sLHid sRHid) i =
      unpackTape (combineWords sLOpen sM sROpen) i := by
  by_cases he : i.val % 2 = 0
  · have hmem : pairOf i ∈ evenOpenSet positions := by
      simp only [evenOpenSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [← index_eq_even i he]
    rw [unpack_even _ i he, unpack_even _ i he]
    unfold mergeWords
    rw [pairSM_combine, pairSL_combine, pairSM_combine, pairSL_combine, ite_eq_left hmem]
  · have hmem : pairOf i ∈ oddOpenSet positions := by
      simp only [oddOpenSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [← index_eq_odd i he]
    rw [unpack_odd _ i he, unpack_odd _ i he]
    unfold mergeWords
    rw [pairSR_combine, pairSM_combine, pairSR_combine, pairSM_combine, ite_eq_left hmem]

theorem unpack_merge_hidden_even (positions : Positions)
    (sLOpen : PairIndex → BitVec 128) (sM : PairIndex → BitVec 64) (sROpen : PairIndex → BitVec 128)
    (sLHid sRHid : PairIndex → BitVec 128) (i : Index) (hi : i ∉ positions) (he : i.val % 2 = 0) :
    unpackTape (mergeWords positions sLOpen sM sROpen sLHid sRHid) i =
      sM (pairOf i) ++ sLHid (pairOf i) := by
  have hnmem : pairOf i ∉ evenOpenSet positions := by
    simp only [evenOpenSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rwa [← index_eq_even i he]
  rw [unpack_even _ i he]
  unfold mergeWords
  rw [pairSM_combine, pairSL_combine, ite_eq_right hnmem]

theorem unpack_merge_hidden_odd (positions : Positions)
    (sLOpen : PairIndex → BitVec 128) (sM : PairIndex → BitVec 64) (sROpen : PairIndex → BitVec 128)
    (sLHid sRHid : PairIndex → BitVec 128) (i : Index) (hi : i ∉ positions) (ho : i.val % 2 ≠ 0) :
    unpackTape (mergeWords positions sLOpen sM sROpen sLHid sRHid) i =
      sRHid (pairOf i) ++ sM (pairOf i) := by
  have hnmem : pairOf i ∉ oddOpenSet positions := by
    simp only [oddOpenSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rwa [← index_eq_odd i ho]
  rw [unpack_odd _ i ho]
  unfold mergeWords
  rw [pairSR_combine, pairSM_combine, ite_eq_right hnmem]

/-- Uniform pair words are five independent uniform functions: the revealed
parts and the private halves. -/
theorem merge_uniform_bind (positions : Positions) {α : Type}
    (next : (PairIndex → Late.PairCoins) → ProbComp α) :
    𝒟[do let sLOpen ← $ᵗ (PairIndex → BitVec 128)
         let sM ← $ᵗ (PairIndex → BitVec 64)
         let sROpen ← $ᵗ (PairIndex → BitVec 128)
         let sLHid ← $ᵗ (PairIndex → BitVec 128)
         let sRHid ← $ᵗ (PairIndex → BitVec 128)
         next (mergeWords positions sLOpen sM sROpen sLHid sRHid)] =
    𝒟[($ᵗ (PairIndex → Late.PairCoins)) >>= next] := by
  unfold mergeWords
  rw [← combine_uniform_bind next]
  rw [← merge_function_bind (evenOpenSet positions) (fun sL =>
    do let sM ← $ᵗ (PairIndex → BitVec 64)
       let sR ← $ᵗ (PairIndex → BitVec 128)
       next (combineWords sL sM sR))]
  apply _root_.evalDist_bind_congr; intro sLOpen
  rw [distribution_bind_comm ($ᵗ (PairIndex → BitVec 128)) ($ᵗ (PairIndex → BitVec 64))
    (fun sLHid sM => ($ᵗ (PairIndex → BitVec 128)) >>= fun sR =>
      next (combineWords (fun j => if j ∈ evenOpenSet positions then sLOpen j else sLHid j) sM sR))]
  apply _root_.evalDist_bind_congr; intro sM
  trans 𝒟[do let sLHid ← $ᵗ (PairIndex → BitVec 128)
             let sROpen ← $ᵗ (PairIndex → BitVec 128)
             let sRHid ← $ᵗ (PairIndex → BitVec 128)
             next (combineWords (fun j => if j ∈ evenOpenSet positions then sLOpen j else sLHid j)
               sM (fun j => if j ∈ oddOpenSet positions then sROpen j else sRHid j))]
  · exact distribution_bind_comm ($ᵗ (PairIndex → BitVec 128)) ($ᵗ (PairIndex → BitVec 128))
      (fun sROpen sLHid => ($ᵗ (PairIndex → BitVec 128)) >>= fun sRHid =>
        next (combineWords (fun j => if j ∈ evenOpenSet positions then sLOpen j else sLHid j)
          sM (fun j => if j ∈ oddOpenSet positions then sROpen j else sRHid j)))
  · apply _root_.evalDist_bind_congr; intro sLHid
    exact merge_function_bind (oddOpenSet positions)
      (fun sR => next (combineWords
        (fun j => if j ∈ evenOpenSet positions then sLOpen j else sLHid j) sM sR))

/-! ### Union bounds and uniform targets -/

theorem prEvent_exists_finset_le_sum {α ι : Type} [DecidableEq ι]
    (comp : ProbComp α) (S : Finset ι) (P : ι → α → Prop) :
    prEvent ((fun a => ∃ i ∈ S, P i a) <$> comp) ≤
      ∑ i ∈ S, prEvent ((fun a => P i a) <$> comp) := by
  induction S using Finset.induction_on with
  | empty =>
    have hz : prEvent ((fun a => ∃ i ∈ (∅ : Finset ι), P i a) <$> comp) = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ (fun _ _ ⟨i, hi, _⟩ => Finset.notMem_empty i hi)
    rw [hz]; simp
  | @insert x S hx ih =>
    rw [Finset.sum_insert hx]
    have hsplit : prEvent ((fun a => ∃ i ∈ insert x S, P i a) <$> comp) ≤
        prEvent ((fun a => P x a) <$> comp) + prEvent ((fun a => ∃ i ∈ S, P i a) <$> comp) := by
      refine (prEvent_mono_of_support _ _ _ ?_).trans
        (prEvent_or_le comp (P x) (fun a => ∃ i ∈ S, P i a))
      intro a _ ⟨i, hi, hpa⟩
      rcases Finset.mem_insert.mp hi with rfl | hiS
      · exact Or.inl hpa
      · exact Or.inr ⟨i, hiS, hpa⟩
    exact hsplit.trans (add_le_add le_rfl ih)

theorem prEvent_exists_le_sum {α ι : Type} [Fintype ι] [DecidableEq ι]
    (comp : ProbComp α) (P : ι → α → Prop) :
    prEvent ((fun a => ∃ i : ι, P i a) <$> comp) ≤
      ∑ i : ι, prEvent ((fun a => P i a) <$> comp) := by
  have hle : prEvent ((fun a => ∃ i : ι, P i a) <$> comp) ≤
      prEvent ((fun a => ∃ i ∈ (Finset.univ : Finset ι), P i a) <$> comp) :=
    prEvent_mono_of_support _ _ _ (fun _ _ ⟨i, h⟩ => ⟨i, Finset.mem_univ i, h⟩)
  exact hle.trans (prEvent_exists_finset_le_sum comp Finset.univ P)

theorem prEvent_uniform_eq_target {α : Type} [Fintype α] [DecidableEq α] [SampleableType α]
    (target : α) :
    prEvent ((fun x : α => x = target) <$> ($ᵗ α)) = (1 : ENNReal) / Fintype.card α := by
  rw [SampleableType.prEvent_uniformSample]
  have hfilt : (Finset.univ.filter (fun x : α => x = target)).card = 1 := by
    rw [Finset.filter_eq', ite_eq_left_of_eq_true _ _ (eq_true (Finset.mem_univ _)),
      Finset.card_singleton]
  rw [hfilt, Nat.cast_one]

theorem prEvent_uniform_coord_le {D R : Type} [DecidableEq D] [Finite D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)]
    (i0 : D) (p : R → Prop) {ε : ENNReal} (hp : prEvent (p <$> ($ᵗ R)) ≤ ε) :
    prEvent ((fun f : D → R => p (f i0)) <$> ($ᵗ (D → R))) ≤ ε := by
  rw [map_eq_bind_pure_comp, ← id_map (x := ($ᵗ (D → R)) >>= _)]
  change prEvent (id <$> (do let values ← $ᵗ (D → R); pure (p (values i0)))) ≤ ε
  have hswap := (EvalDistEq.of_evalDist_eq
    (uniform_coordinate_bind (D := D) (R := R) i0 (fun f => pure (p (f i0))))).prEvent_eq id
  rw [← hswap]
  apply prEvent_bind_le_of_forall_le_of_support
  intro f _
  have hev : (do let fresh ← $ᵗ R; pure (p (Function.update f i0 fresh i0))) = (p <$> ($ᵗ R)) := by
    simp only [Function.update_self, map_eq_bind_pure_comp]; rfl
  rw [hev, prEvent_map]
  exact hp

theorem prEvent_map_eq_id_bind {α : Type} (mx : ProbComp α) (P : α → Prop) :
    prEvent (P <$> mx) = prEvent (id <$> (mx >>= fun a => pure (P a))) := by
  have h : (mx >>= fun a => pure (P a)) = (P <$> mx) := by
    rw [map_eq_bind_pure_comp]; rfl
  rw [h, prEvent_map]; rfl

theorem prEvent_uniform_coord_cond_le {D R : Type} [DecidableEq D] [Finite D] [Finite R]
    [Nonempty R] [SampleableType R] [SampleableType (D → R)]
    (i0 : D) (P : (D → R) → Prop) {ε : ENNReal}
    (hP : ∀ f : D → R, prEvent ((fun r : R => P (Function.update f i0 r)) <$> ($ᵗ R)) ≤ ε) :
    prEvent (P <$> ($ᵗ (D → R))) ≤ ε := by
  rw [prEvent_map_eq_id_bind]
  have hswap := (EvalDistEq.of_evalDist_eq
    (uniform_coordinate_bind (D := D) (R := R) i0 (fun f => pure (P f)))).prEvent_eq id
  rw [← hswap]
  apply prEvent_bind_le_of_forall_le; intro f
  have hev : (do let r ← $ᵗ R; pure (P (Function.update f i0 r))) =
      ((fun r : R => P (Function.update f i0 r)) <$> ($ᵗ R)) := by
    rw [map_eq_bind_pure_comp]; rfl
  rw [hev, prEvent_map]
  exact hP f

theorem prEvent_prod_fst_le {A B : Type} [SampleableType A] [SampleableType B]
    (P : A → Prop) {ε : ENNReal} (hP : prEvent (P <$> ($ᵗ A)) ≤ ε) :
    prEvent ((fun p : A × B => P p.1) <$> ($ᵗ (A × B))) ≤ ε := by
  have hp : 𝒟[(fun p : A × B => P p.1) <$> ($ᵗ (A × B))] = 𝒟[P <$> ($ᵗ A)] := by
    rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    change 𝒟[($ᵗ (A × B)) >>= fun p => pure (P p.1)] = 𝒟[($ᵗ A) >>= fun a => pure (P a)]
    rw [← prod_uniform_bind (fun p : A × B => pure (P p.1))]
    apply _root_.evalDist_bind_congr; intro a
    exact OracleComp.evalDist_bind_const ($ᵗ B) (pure (P a))
  have hpr := (EvalDistEq.of_evalDist_eq hp).prEvent_eq id
  rw [prEvent_map, prEvent_map] at hpr
  exact (le_of_eq hpr).trans hP

theorem prEvent_prod_snd_le {A B : Type} [SampleableType A] [SampleableType B]
    (P : B → Prop) {ε : ENNReal} (hP : prEvent (P <$> ($ᵗ B)) ≤ ε) :
    prEvent ((fun p : A × B => P p.2) <$> ($ᵗ (A × B))) ≤ ε := by
  have hp : 𝒟[(fun p : A × B => P p.2) <$> ($ᵗ (A × B))] = 𝒟[P <$> ($ᵗ B)] := by
    rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
    change 𝒟[($ᵗ (A × B)) >>= fun p => pure (P p.2)] = 𝒟[($ᵗ B) >>= fun b => pure (P b)]
    rw [← prod_uniform_bind (fun p : A × B => pure (P p.2))]
    exact OracleComp.evalDist_bind_const ($ᵗ A) (($ᵗ B) >>= fun b => pure (P b))
  have hpr := (EvalDistEq.of_evalDist_eq hp).prEvent_eq id
  rw [prEvent_map, prEvent_map] at hpr
  exact (le_of_eq hpr).trans hP

theorem prEvent_bind_fst_mid_snd {A B C : Type}
    [SampleableType A] [SampleableType B] [SampleableType C]
    (P : B → Prop) {ε : ENNReal} (hP : prEvent (P <$> ($ᵗ B)) ≤ ε) :
    prEvent (id <$> (do let _ ← $ᵗ A; let b ← $ᵗ B; let _ ← $ᵗ C; pure (P b))) ≤ ε := by
  apply prEvent_bind_le_of_forall_le; intro _
  have h : 𝒟[do let b ← $ᵗ B; let _ ← $ᵗ C; pure (P b)] = 𝒟[P <$> ($ᵗ B)] := by
    rw [map_eq_bind_pure_comp]
    apply _root_.evalDist_bind_congr; intro b
    exact OracleComp.evalDist_bind_const ($ᵗ C) (pure (P b))
  have hpr := (EvalDistEq.of_evalDist_eq h).prEvent_eq id
  rw [prEvent_map] at hpr
  exact (le_of_eq hpr).trans hP

private theorem card_ratio :
    ((2 ^ 128 : Nat) : ENNReal) / ((2 ^ 320 : Nat) : ENNReal) = 1 / 2 ^ 192 := by
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [show (2 : ENNReal) ^ 320 = 2 ^ 128 * 2 ^ 192 by rw [← pow_add],
    ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl (pow_ne_zero 128 two_ne_zero))
      (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)),
    mul_comm ((2 : ENNReal) ^ 128)⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel (pow_ne_zero 128 two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
    mul_one, one_div]

/-- The even leaf's salt of a uniform pair word takes each value with probability `2^-192`. -/
theorem pair_salt_even_target (t : Late.Salt) :
    prEvent ((fun r : Late.PairCoins => Late.pairSalts r false = t) <$> ($ᵗ Late.PairCoins)) ≤
      (1 : ENNReal) / 2 ^ 192 := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hinj : Set.InjOn pairSR
      ((Finset.univ.filter (fun r : Late.PairCoins => Late.pairSalts r false = t)) :
        Set Late.PairCoins) := by
    intro a ha b hb hsr
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    have hsm : pairSM a = pairSM b := by
      have heq := ha.2.trans hb.2.symm
      rw [pair_salts_even, pair_salts_even] at heq
      have := congrArg (fun v : Late.Salt => v.extractLsb' 128 64) heq
      simpa only [BitVec.extractLsb'_append_eq_of_le (by decide : 128 ≤ 128), Nat.sub_self,
        BitVec.extractLsb'_eq_self] using this
    have hsl : pairSL a = pairSL b := by
      have heq := ha.2.trans hb.2.symm
      rw [pair_salts_even, pair_salts_even] at heq
      have := congrArg (fun v : Late.Salt => v.extractLsb' 0 128) heq
      simpa only [BitVec.extractLsb'_append_eq_right] using this
    rw [pair_word_parts a, pair_word_parts b, hsr, hsm, hsl]
  have hcard :
      (Finset.univ.filter (fun r : Late.PairCoins => Late.pairSalts r false = t)).card ≤ 2 ^ 128 := by
    calc
      (Finset.univ.filter (fun r : Late.PairCoins => Late.pairSalts r false = t)).card
        ≤ (Finset.univ : Finset (BitVec 128)).card :=
          Finset.card_le_card_of_injOn pairSR (fun _ _ => Finset.mem_univ _) hinj
      _ = 2 ^ 128 := by rw [Finset.card_univ, Fintype.card_bitVec]
  rw [Fintype.card_bitVec 320]
  exact (ENNReal.div_le_div_right (Nat.cast_le.mpr hcard) _).trans (le_of_eq card_ratio)

/-- The odd leaf's salt of a uniform pair word takes each value with probability `2^-192`. -/
theorem pair_salt_odd_target (t : Late.Salt) :
    prEvent ((fun r : Late.PairCoins => Late.pairSalts r true = t) <$> ($ᵗ Late.PairCoins)) ≤
      (1 : ENNReal) / 2 ^ 192 := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hinj : Set.InjOn pairSL
      ((Finset.univ.filter (fun r : Late.PairCoins => Late.pairSalts r true = t)) :
        Set Late.PairCoins) := by
    intro a ha b hb hsl
    rw [Finset.mem_coe, Finset.mem_filter] at ha hb
    have hsr : pairSR a = pairSR b := by
      have heq := ha.2.trans hb.2.symm
      rw [pair_salts_odd, pair_salts_odd] at heq
      have := congrArg (fun v : Late.Salt => v.extractLsb' 64 128) heq
      simpa only [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 64), Nat.sub_self,
        BitVec.extractLsb'_eq_self] using this
    have hsm : pairSM a = pairSM b := by
      have heq := ha.2.trans hb.2.symm
      rw [pair_salts_odd, pair_salts_odd] at heq
      have := congrArg (fun v : Late.Salt => v.extractLsb' 0 64) heq
      simpa only [BitVec.extractLsb'_append_eq_right] using this
    rw [pair_word_parts a, pair_word_parts b, hsr, hsm, hsl]
  have hcard :
      (Finset.univ.filter (fun r : Late.PairCoins => Late.pairSalts r true = t)).card ≤ 2 ^ 128 := by
    calc
      (Finset.univ.filter (fun r : Late.PairCoins => Late.pairSalts r true = t)).card
        ≤ (Finset.univ : Finset (BitVec 128)).card :=
          Finset.card_le_card_of_injOn pairSL (fun _ _ => Finset.mem_univ _) hinj
      _ = 2 ^ 128 := by rw [Finset.card_univ, Fintype.card_bitVec]
  rw [Fintype.card_bitVec 320]
  exact (ENNReal.div_le_div_right (Nat.cast_le.mpr hcard) _).trans (le_of_eq card_ratio)

/-- **Each leaf's salt is uniform on its own.** The shared midpoint couples the
two salts of a pair, but either one alone still has 192 uniform bits. -/
theorem salt_target_le (i : Index) (t : Late.Salt) :
    prEvent ((fun words : PairIndex → Late.PairCoins => unpackTape words i = t) <$>
      ($ᵗ (PairIndex → Late.PairCoins))) ≤ (1 : ENNReal) / 2 ^ 192 := by
  change prEvent ((fun words : PairIndex → Late.PairCoins =>
    Late.pairSalts (words (pairOf i)) (i.val.testBit 0) = t) <$> _) ≤ _
  cases i.val.testBit 0
  · exact prEvent_uniform_coord_le (D := PairIndex) (R := Late.PairCoins) (pairOf i)
      (fun r => Late.pairSalts r false = t) (pair_salt_even_target t)
  · exact prEvent_uniform_coord_le (D := PairIndex) (R := Late.PairCoins) (pairOf i)
      (fun r => Late.pairSalts r true = t) (pair_salt_odd_target t)

end CommitGolfCandidate.LateHiding
