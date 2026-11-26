import CommitGolfCandidate.MoonBinding
import CommitGolfCandidate.HidingTrace
import Mathlib.Data.Fintype.EquivFin

/-! Core probabilistic, ROM-caching, and bottom-up tree-query primitives for the
paired late-salt (SM-PLS-40) statistical hiding proof:
- `splitBlocks` & `combinePairRand`: bijection between bulk RANDOM(40) bits and `(sL, sM, sR)`
- `mergePairRand`: exact split of `(sL, sM, sR)` into opened coordinates + secret `(sL_hid, sR_hid)`
- Lazy-ROM 192-bit slice hit bounds (`start = 0` for odd salts, `start = 64` for even salts)
- `queryAllUnsalted` (`3 * LENGTH` unsalted leaf calls `u, a, b`) cached prior to salt sampling
- `queryIdealTree` (opened Call-3s + L1..L24 internal nodes) and its deterministic `GoodIdealTrace` invariant. -/
namespace CommitGolfCandidate

local instance moonHidingCoreDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

/-! ### 1. Pair Indices, Bulk RANDOM Splitting, and Opened/Hidden Salt Split -/

abbrev PairIdx := Fin (LENGTH / 2)

def evenIdx (j : PairIdx) : Index :=
  ⟨2 * j.val, by have := j.isLt; unfold LENGTH LOG_LENGTH at *; omega⟩

def oddIdx (j : PairIdx) : Index :=
  ⟨2 * j.val + 1, by have := j.isLt; unfold LENGTH LOG_LENGTH at *; omega⟩

def pairOf (i : Index) : PairIdx :=
  ⟨i.val / 2, by have := i.isLt; unfold LENGTH LOG_LENGTH at *; omega⟩

theorem evenIdx_val (j : PairIdx) : (evenIdx j).val = 2 * j.val := rfl
theorem oddIdx_val (j : PairIdx) : (oddIdx j).val = 2 * j.val + 1 := rfl
theorem pairOf_evenIdx (j : PairIdx) : pairOf (evenIdx j) = j := Fin.ext (by simp [pairOf, evenIdx])
theorem pairOf_oddIdx (j : PairIdx) : pairOf (oddIdx j) = j := Fin.ext (by simp [pairOf, oddIdx]; omega)

theorem index_eq_even_of_mod (i : Index) (he : i.val % 2 = 0) : i = evenIdx (pairOf i) :=
  Fin.ext (by simp [evenIdx, pairOf]; omega)

theorem index_eq_odd_of_mod (i : Index) (ho : i.val % 2 ≠ 0) : i = oddIdx (pairOf i) :=
  Fin.ext (by simp [oddIdx, pairOf]; omega)

def splitBlocks (width count : Nat) (packed : BitVec (width * count)) : Fin count → BitVec width :=
  fun index => packed.extractLsb' (width * index.val) width

theorem split_blocks_injective (width count : Nat) (pos : 0 < width) :
    Function.Injective (splitBlocks width count) := by
  intro left right same
  apply BitVec.eq_of_getLsbD_eq
  intro bit below
  have block : bit / width < count := (Nat.div_lt_iff_lt_mul pos).mpr (by simpa [Nat.mul_comm] using below)
  have offset : bit % width < width := Nat.mod_lt _ pos
  have aligned : width * (bit / width) + bit % width = bit := Nat.div_add_mod bit width
  have heq := congrArg (fun v : BitVec width => v.getLsbD (bit % width)) (congrFun same ⟨bit / width, block⟩)
  simpa only [splitBlocks, BitVec.getLsbD_extractLsb', offset, decide_true, Bool.true_and, aligned] using heq

theorem split_blocks_bijective (width count : Nat) (pos : 0 < width) :
    Function.Bijective (splitBlocks width count) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨split_blocks_injective width count pos, ?_⟩
  have hc (n : Nat) : Fintype.card (BitVec n) = 2 ^ n := Fintype.card_bitVec n
  simp only [Fintype.card_fun, Fintype.card_fin, hc]
  exact pow_mul 2 width count

theorem split_blocks_uniform_bind (width count : Nat) (pos : 0 < width)
    [SampleableType (Fin count → BitVec width)]
    {α : Type} (next : (Fin count → BitVec width) → ProbComp α) :
    𝒟[($ᵗ BitVec (width * count)) >>= fun packed => next (splitBlocks width count packed)] =
      𝒟[($ᵗ (Fin count → BitVec width)) >>= next] := by
  rw [← bind_map_left]
  exact ((SampleableType.map_uniformSample_evalDistEq_of_bijective
    (split_blocks_bijective width count pos)).bind_left next).evalDist_eq

def combinePairRand
    (sL : PairIdx → BitVec 128) (sM : PairIdx → BitVec 64) (sR : PairIdx → BitVec 128) :
    PairIdx → PairRand :=
  fun j => (sR j ++ sM j) ++ sL j

theorem pairSL_combine (sL : PairIdx → BitVec 128) (sM : PairIdx → BitVec 64)
    (sR : PairIdx → BitVec 128) (j : PairIdx) :
    pairSL (combinePairRand sL sM sR j) = sL j := by
  unfold pairSL combinePairRand
  exact BitVec.extractLsb'_append_eq_right

theorem pairSM_combine (sL : PairIdx → BitVec 128) (sM : PairIdx → BitVec 64)
    (sR : PairIdx → BitVec 128) (j : PairIdx) :
    pairSM (combinePairRand sL sM sR j) = sM j := by
  unfold pairSM combinePairRand
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 128 ≤ 128)]
  exact BitVec.extractLsb'_append_eq_right

theorem pairSR_combine (sL : PairIdx → BitVec 128) (sM : PairIdx → BitVec 64)
    (sR : PairIdx → BitVec 128) (j : PairIdx) :
    pairSR (combinePairRand sL sM sR j) = sR j := by
  unfold pairSR combinePairRand
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 128 ≤ 192)]
  rw [BitVec.extractLsb'_append_eq_of_le (by decide : 64 ≤ 192 - 128)]
  simpa using BitVec.extractLsb'_eq_self (x := sR j)

theorem pairSaltEven_combine (sL : PairIdx → BitVec 128) (sM : PairIdx → BitVec 64)
    (sR : PairIdx → BitVec 128) (j : PairIdx) :
    pairSaltEven (combinePairRand sL sM sR j) = sM j ++ sL j := by
  rw [pairSaltEven_eq, pairSM_combine, pairSL_combine]

theorem pairSaltOdd_combine (sL : PairIdx → BitVec 128) (sM : PairIdx → BitVec 64)
    (sR : PairIdx → BitVec 128) (j : PairIdx) :
    pairSaltOdd (combinePairRand sL sM sR j) = sR j ++ sM j := by
  rw [pairSaltOdd_eq, pairSR_combine, pairSM_combine]

theorem combinePairRand_bijective :
    Function.Bijective (fun p : (PairIdx → BitVec 128) × (PairIdx → BitVec 64) × (PairIdx → BitVec 128) =>
      combinePairRand p.1 p.2.1 p.2.2) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨fun r => (fun j => pairSL (r j), fun j => pairSM (r j), fun j => pairSR (r j)), ?_, ?_⟩
  · rintro ⟨sL, sM, sR⟩
    refine Prod.ext (funext fun j => pairSL_combine sL sM sR j)
      (Prod.ext (funext fun j => pairSM_combine sL sM sR j) (funext fun j => pairSR_combine sL sM sR j))
  · intro r; funext j; exact (pairRand_eq_parts (r j)).symm

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

theorem tripleBijection_uniform_bind {A B C D α : Type}
    [SampleableType A] [SampleableType B] [SampleableType C] [SampleableType D]
    (f : A × B × C → D) (hf : Function.Bijective f) (next : D → ProbComp α) :
    𝒟[do let a ← $ᵗ A
         let b ← $ᵗ B
         let c ← $ᵗ C
         next (f (a, b, c))] =
    𝒟[($ᵗ D) >>= next] := by
  have hbij := ((SampleableType.map_uniformSample_evalDistEq_of_bijective hf).bind_left next).evalDist_eq
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

theorem combinePairRand_uniform_bind {α : Type} (next : (PairIdx → PairRand) → ProbComp α) :
    𝒟[do let sL ← $ᵗ (PairIdx → BitVec 128)
         let sM ← $ᵗ (PairIdx → BitVec 64)
         let sR ← $ᵗ (PairIdx → BitVec 128)
         next (combinePairRand sL sM sR)] =
    𝒟[($ᵗ (PairIdx → PairRand)) >>= next] :=
  tripleBijection_uniform_bind
    (fun p : (PairIdx → BitVec 128) × (PairIdx → BitVec 64) × (PairIdx → BitVec 128) =>
      combinePairRand p.1 p.2.1 p.2.2)
    combinePairRand_bijective next

theorem funMerge_uniform_bind {D R α : Type} [DecidableEq D]
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

def evenOpenSet (positions : Positions) : Finset PairIdx :=
  Finset.univ.filter (fun j => evenIdx j ∈ positions)

def oddOpenSet (positions : Positions) : Finset PairIdx :=
  Finset.univ.filter (fun j => oddIdx j ∈ positions)

def mergePairRand (positions : Positions)
    (sLOpen : PairIdx → BitVec 128) (sM : PairIdx → BitVec 64) (sROpen : PairIdx → BitVec 128)
    (sLHid sRHid : PairIdx → BitVec 128) : PairIdx → PairRand :=
  combinePairRand
    (fun j => if j ∈ evenOpenSet positions then sLOpen j else sLHid j)
    sM
    (fun j => if j ∈ oddOpenSet positions then sROpen j else sRHid j)

theorem mergePairRand_opened_salt (positions : Positions)
    (sLOpen : PairIdx → BitVec 128) (sM : PairIdx → BitVec 64) (sROpen : PairIdx → BitVec 128)
    (sLHid sRHid : PairIdx → BitVec 128) (i : Index) (hi : i ∈ positions) :
    pairSalts (mergePairRand positions sLOpen sM sROpen sLHid sRHid) i =
      pairSalts (combinePairRand sLOpen sM sROpen) i := by
  unfold pairSalts mergePairRand
  dsimp only
  split_ifs with he
  · have hmem : pairOf i ∈ evenOpenSet positions := by
      simp only [evenOpenSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [← index_eq_even_of_mod i he]
    change pairSaltEven (combinePairRand _ sM _ (pairOf i)) = pairSaltEven (combinePairRand sLOpen sM sROpen (pairOf i))
    rw [pairSaltEven_combine, pairSaltEven_combine, if_pos hmem]
  · have hmem : pairOf i ∈ oddOpenSet positions := by
      simp only [oddOpenSet, Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [← index_eq_odd_of_mod i he]
    change pairSaltOdd (combinePairRand _ sM _ (pairOf i)) = pairSaltOdd (combinePairRand sLOpen sM sROpen (pairOf i))
    rw [pairSaltOdd_combine, pairSaltOdd_combine, if_pos hmem]

theorem mergePairRand_hidden_even (positions : Positions)
    (sLOpen : PairIdx → BitVec 128) (sM : PairIdx → BitVec 64) (sROpen : PairIdx → BitVec 128)
    (sLHid sRHid : PairIdx → BitVec 128) (i : Index) (hi : i ∉ positions) (he : i.val % 2 = 0) :
    pairSalts (mergePairRand positions sLOpen sM sROpen sLHid sRHid) i =
      sM (pairOf i) ++ sLHid (pairOf i) := by
  have hnmem : pairOf i ∉ evenOpenSet positions := by
    simp only [evenOpenSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rwa [← index_eq_even_of_mod i he]
  unfold pairSalts mergePairRand
  dsimp only
  rw [if_pos he]
  change pairSaltEven (combinePairRand _ sM _ (pairOf i)) = _
  rw [pairSaltEven_combine, if_neg hnmem]

theorem mergePairRand_hidden_odd (positions : Positions)
    (sLOpen : PairIdx → BitVec 128) (sM : PairIdx → BitVec 64) (sROpen : PairIdx → BitVec 128)
    (sLHid sRHid : PairIdx → BitVec 128) (i : Index) (hi : i ∉ positions) (ho : i.val % 2 ≠ 0) :
    pairSalts (mergePairRand positions sLOpen sM sROpen sLHid sRHid) i =
      sRHid (pairOf i) ++ sM (pairOf i) := by
  have hnmem : pairOf i ∉ oddOpenSet positions := by
    simp only [oddOpenSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rwa [← index_eq_odd_of_mod i ho]
  unfold pairSalts mergePairRand
  dsimp only
  rw [if_neg ho]
  change pairSaltOdd (combinePairRand _ sM _ (pairOf i)) = _
  rw [pairSaltOdd_combine, if_neg hnmem]

theorem mergePairRand_uniform_bind (positions : Positions) {α : Type}
    (next : (PairIdx → PairRand) → ProbComp α) :
    𝒟[do let sLOpen ← $ᵗ (PairIdx → BitVec 128)
         let sM ← $ᵗ (PairIdx → BitVec 64)
         let sROpen ← $ᵗ (PairIdx → BitVec 128)
         let sLHid ← $ᵗ (PairIdx → BitVec 128)
         let sRHid ← $ᵗ (PairIdx → BitVec 128)
         next (mergePairRand positions sLOpen sM sROpen sLHid sRHid)] =
    𝒟[($ᵗ (PairIdx → PairRand)) >>= next] := by
  unfold mergePairRand
  rw [← combinePairRand_uniform_bind next]
  rw [← funMerge_uniform_bind (evenOpenSet positions) (fun sL =>
    do let sM ← $ᵗ (PairIdx → BitVec 64)
       let sR ← $ᵗ (PairIdx → BitVec 128)
       next (combinePairRand sL sM sR))]
  apply _root_.evalDist_bind_congr; intro sLOpen
  rw [distribution_bind_comm ($ᵗ (PairIdx → BitVec 128)) ($ᵗ (PairIdx → BitVec 64))
    (fun sLHid sM => ($ᵗ (PairIdx → BitVec 128)) >>= fun sR =>
      next (combinePairRand (fun j => if j ∈ evenOpenSet positions then sLOpen j else sLHid j) sM sR))]
  apply _root_.evalDist_bind_congr; intro sM
  trans 𝒟[do let sLHid ← $ᵗ (PairIdx → BitVec 128)
             let sROpen ← $ᵗ (PairIdx → BitVec 128)
             let sRHid ← $ᵗ (PairIdx → BitVec 128)
             next (combinePairRand (fun j => if j ∈ evenOpenSet positions then sLOpen j else sLHid j)
               sM (fun j => if j ∈ oddOpenSet positions then sROpen j else sRHid j))]
  · exact distribution_bind_comm ($ᵗ (PairIdx → BitVec 128)) ($ᵗ (PairIdx → BitVec 128))
      (fun sROpen sLHid => ($ᵗ (PairIdx → BitVec 128)) >>= fun sRHid =>
        next (combinePairRand (fun j => if j ∈ evenOpenSet positions then sLOpen j else sLHid j)
          sM (fun j => if j ∈ oddOpenSet positions then sROpen j else sRHid j)))
  · apply _root_.evalDist_bind_congr; intro sLHid
    exact funMerge_uniform_bind (oddOpenSet positions)
      (fun sR => next (combinePairRand (fun j => if j ∈ evenOpenSet positions then sLOpen j else sLHid j) sM sR))

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
      SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample index (fun values : D → R => values)
  trans 𝒟[do let value ← $ᵗ R
              let values ← $ᵗ (D → R)
              next (Function.update values index value)]
  · exact distribution_bind_comm _ _ _
  · trans 𝒟[(do let value ← $ᵗ R
                let values ← $ᵗ (D → R)
                pure (Function.update values index value)) >>= next]
    · simp only [bind_assoc, pure_bind]
    · rw [evalDist_bind_of_discrete, marginal, ← evalDist_bind_of_discrete]

/-! ### 2. Stage-1 Lazy Sampling & Cache Coverage -/

theorem staged_compression_sampling (permutation : Perm) {α β : Type}
    (first : OracleComp World α) (next : α → OracleComp World β) :
    𝒟[do let table ← $ᵗ Compression
         fixedOracleRun ⟨table, permutation⟩ (first >>= next)] =
    𝒟[do let (value, cache) ← compressionRun permutation first ∅
         let table ← $ᵗ Compression
         fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next value)] := by
  rw [← compression_sampling_empty, compression_run_bind, map_bind]
  apply _root_.evalDist_bind_congr
  rintro ⟨value, cache⟩
  exact compression_sampling_equivalence permutation (next value) cache

theorem compression_cache_covered (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) (cache : CompressionCache)
    (known : Finset CompressionSpec.Domain) (covered : ∀ key, cache key ≠ none → key ∈ known)
    (result : α × CompressionCache)
    (reached : result ∈ support (compressionRun permutation computation cache)) :
    ∃ keys : Finset CompressionSpec.Domain, keys.card ≤ known.card + budget ∧
      ∀ key, result.2 key ≠ none → key ∈ keys := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget cache known result with
  | pure value =>
    rw [compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact ⟨known, by omega, covered⟩
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · rw [compression_run_private] at reached
      obtain ⟨answer, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
      exact ih answer budget (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 answer)
        cache known covered result reached
    · have positive : 1 ≤ budget := bounded.1
      have tails : ∀ answer, PublicQueryBound (next answer) (budget - 1) := bounded.2
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress] at reached
        cases cached : cache input with
        | some answer =>
          rw [cached] at reached
          obtain ⟨keys, size, covers⟩ := ih answer (budget - 1) (tails answer) cache known covered result reached
          exact ⟨keys, by omega, covers⟩
        | none =>
          rw [cached] at reached
          obtain ⟨answer, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
          have nextCovered : ∀ key, (cache.cacheQuery input answer) key ≠ none →
              key ∈ insert input known := by
            intro key populated
            by_cases same : key = input
            · exact same ▸ Finset.mem_insert_self _ _
            · rw [QueryCache.cacheQuery_of_ne _ _ same] at populated
              exact Finset.mem_insert_of_mem (covered key populated)
          obtain ⟨keys, size, covers⟩ := ih answer (budget - 1) (tails answer)
            (cache.cacheQuery input answer) (insert input known) nextCovered result reached
          have inserted := Finset.card_insert_le input known
          exact ⟨keys, by omega, covers⟩
      · rcases permQuery with input | input
        · rw [compression_run_permute] at reached
          obtain ⟨keys, size, covers⟩ := ih _ (budget - 1) (tails _) cache known covered result reached
          exact ⟨keys, by omega, covers⟩
        · rw [compression_run_inverse] at reached
          obtain ⟨keys, size, covers⟩ := ih _ (budget - 1) (tails _) cache known covered result reached
          exact ⟨keys, by omega, covers⟩

theorem first_stage_cache_bound (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) (result : α × CompressionCache)
    (reached : result ∈ support (compressionRun permutation computation ∅)) :
    ∃ keys : Finset CompressionSpec.Domain, keys.card ≤ budget ∧
      ∀ key, result.2 key ≠ none → key ∈ keys := by
  have r := compression_cache_covered permutation computation budget bounded ∅ ∅ (by simp) result reached
  simpa only [Finset.card_empty, Nat.zero_add] using r

theorem staged_observe_query_bound {State Output : Type} {openingSize budget : Nat}
    (permutation : Perm) (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget)
    (result : Hiding.HidingChallenge State openingSize × CompressionCache)
    (reached : result ∈ support (compressionRun permutation adversary.choose ∅))
    (root : Commitment) (proof : Proof) :
    PublicQueryBound (adversary.observe result.1.aux root proof) budget := by
  have projected : result.1 ∈ support
      ((simulateQ (compressionHandler permutation) adversary.choose).run' ∅) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨result, reached, rfl⟩
  have possible := support_simulateQ_run'_subset (compressionHandler permutation) adversary.choose ∅ projected
  have instrumented : result.1 ∈ support (Prod.fst <$> Hiding.counted adversary.choose) := by
    have projection : Prod.fst <$> Hiding.counted adversary.choose = adversary.choose :=
      fst_map_costDist adversary.choose ⟨Oracle.callCost⟩
    rw [projection]
    exact possible
  rw [support_map] at instrumented
  obtain ⟨⟨challenge, calls⟩, counted, equal⟩ := instrumented
  change challenge = result.1 at equal
  subst challenge
  exact (hiding_observe_query_bound adversary bounded (result.1, calls) counted root proof).mono
    (Nat.sub_le _ _)

theorem distance_bind_le_averaged_bad {Key Output : Type} [Fintype Key]
    (keys : ProbComp Key) (left right : Key → ProbComp Output)
    (tagged : Key → ProbComp (Output × Unit × Bool))
    (bounded : ∀ key, measureTVDist (left key) (right key) ≤
      (prEvent ((fun result => result.2.2 = true) <$> (tagged key))).toReal) :
    measureTVDist (keys >>= left) (keys >>= right) ≤
      (prEvent ((fun result => result.2.2 = true) <$> (keys >>= tagged))).toReal := by
  refine (measureTVDist_bind_left_le_tsum keys left right).trans ?_
  rw [tsum_fintype, prEvent_bind_eq_sum_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_le_sum
    intro key _
    rw [ENNReal.toReal_mul]
    exact mul_le_mul_of_nonneg_left (bounded key) ENNReal.toReal_nonneg
  · intro key _
    exact ENNReal.mul_ne_top (prEvent_ne_top _) (prEvent_ne_top _)

/-! ### 3. BitVec Helpers & Lazy-ROM 192-bit Slice Hit Bounds (`start = 0` or `64`) -/

theorem extractLsb'_cast_eq {m n : Nat} (h : m = n) (x : BitVec m) (start len : Nat) :
    (x.cast h).extractLsb' start len = x.extractLsb' start len := by
  subst h; rfl

theorem extractLsb'_0_192_append_digest {m : Nat} (hi : BitVec m) (lo : Digest) :
    (hi ++ lo).extractLsb' 0 192 = lo.extractLsb' 0 192 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.zero_add,
    hb, decide_true, Bool.true_and, show b < 256 by omega, ite_true]

theorem extractLsb'_576_192_ternary (d0 d1 d2 : Digest) :
    (ternaryInput d0 d1 d2).extractLsb' 576 192 = d2.extractLsb' 64 192 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  unfold ternaryInput
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hb, decide_true, Bool.true_and,
    show ¬ (576 + b < 256) by omega, show ¬ (576 + b - 256 < 256) by omega, ite_false,
    show 576 + b - 256 - 256 = 64 + b by omega]

theorem extractLsb'_576_192_ternary_zero (d0 d1 : Digest) :
    (ternaryInput d0 d1 0).extractLsb' 576 192 = 0#192 := by
  rw [extractLsb'_576_192_ternary]
  apply BitVec.eq_of_getLsbD_eq
  intro b _
  change ((0#256).extractLsb' 64 192).getLsbD b = (0#192).getLsbD b
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_zero, Bool.and_false]

theorem fixed_oracle_run_compress (oracle : Oracle) {α : Type}
    (x : BitVec COMPRESSION_INPUT_LENGTH) (next : Digest → OracleComp World α) :
    fixedOracleRun oracle ((liftM (World.query (.inr (.inl x))) : OracleComp World Digest) >>= next) =
      fixedOracleRun oracle (next (oracle.compression x)) :=
  fixed_oracle_run_public oracle (.inl x) next

def CacheHitsSlice192 (start : Nat) (cache : CompressionCache) (targets : Finset (BitVec 192)) : Prop :=
  ∃ (k : BitVec COMPRESSION_INPUT_LENGTH) (ans : Digest),
    cache k = some ans ∧ ans.extractLsb' start 192 ∈ targets

private theorem card_slice192_preimage (start : Nat) (hstart : start = 0 ∨ start = 64)
    (targets : Finset (BitVec 192))
    [DecidablePred (fun ans : Digest => ans.extractLsb' start 192 ∈ targets)] :
    (Finset.univ.filter (fun ans : Digest => ans.extractLsb' start 192 ∈ targets)).card ≤
      2 ^ 64 * targets.card := by
  let rest : Digest → BitVec 64 := fun ans =>
    if start = 0 then ans.extractLsb' 192 64 else ans.extractLsb' 0 64
  have hinj : Set.InjOn (fun ans : Digest => (rest ans, ans.extractLsb' start 192))
      (Finset.univ.filter (fun ans : Digest => ans.extractLsb' start 192 ∈ targets) : Set Digest) := by
    intro a _ b _ h
    have hr : rest a = rest b := congrArg Prod.fst h
    have hs : a.extractLsb' start 192 = b.extractLsb' start 192 := congrArg Prod.snd h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rcases hstart with rfl | rfl
    · simp only [rest, ite_true] at hr
      by_cases h192 : i < 192
      · have := congrArg (fun v : BitVec 192 => v.getLsbD i) hs
        simpa only [BitVec.getLsbD_extractLsb', h192, decide_true, Bool.true_and, Nat.zero_add] using this
      · have hi64 : i - 192 < 64 := by omega
        have := congrArg (fun v : BitVec 64 => v.getLsbD (i - 192)) hr
        simpa only [BitVec.getLsbD_extractLsb', hi64, decide_true, Bool.true_and,
          show 192 + (i - 192) = i by omega] using this
    · simp only [rest, show (64 : Nat) ≠ 0 by decide, ite_false] at hr
      by_cases h64 : i < 64
      · have := congrArg (fun v : BitVec 64 => v.getLsbD i) hr
        simpa only [BitVec.getLsbD_extractLsb', h64, decide_true, Bool.true_and, Nat.zero_add] using this
      · have hi192 : i - 64 < 192 := by omega
        have := congrArg (fun v : BitVec 192 => v.getLsbD (i - 64)) hs
        simpa only [BitVec.getLsbD_extractLsb', hi192, decide_true, Bool.true_and,
          show 64 + (i - 64) = i by omega] using this
  have hmaps : Set.MapsTo (fun ans : Digest => (rest ans, ans.extractLsb' start 192))
      (Finset.univ.filter (fun ans : Digest => ans.extractLsb' start 192 ∈ targets) : Set Digest)
      ((Finset.univ ×ˢ targets : Finset (BitVec 64 × BitVec 192)) : Set (BitVec 64 × BitVec 192)) := by
    intro ans hans
    rw [Finset.mem_coe, Finset.mem_filter] at hans
    rw [Finset.mem_coe, Finset.mem_product]
    exact ⟨Finset.mem_univ _, hans.2⟩
  calc
    (Finset.univ.filter (fun ans : Digest => ans.extractLsb' start 192 ∈ targets)).card
      ≤ (Finset.univ ×ˢ targets : Finset (BitVec 64 × BitVec 192)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (Finset.univ : Finset (BitVec 64)).card * targets.card := Finset.card_product _ _
    _ = 2 ^ 64 * targets.card := by rw [Finset.card_univ, Fintype.card_bitVec]

theorem uniform_digest_hits_slice192_le (start : Nat) (hstart : start = 0 ∨ start = 64)
    (targets : Finset (BitVec 192)) :
    (prEvent ((fun ans : Digest => ans.extractLsb' start 192 ∈ targets) <$> ($ᵗ Digest))) ≤
      (targets.card : ENNReal) / 2 ^ 192 := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hcard : Fintype.card Digest = 2 ^ 256 := Fintype.card_bitVec 256
  rw [hcard]
  calc
    ((Finset.univ.filter (fun ans : Digest => ans.extractLsb' start 192 ∈ targets)).card : ENNReal) / (2 ^ 256 : Nat)
      ≤ ((2 ^ 64 * targets.card : Nat) : ENNReal) / (2 ^ 256 : Nat) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr (card_slice192_preimage start hstart targets)) _
    _ = (targets.card : ENNReal) / 2 ^ 192 := by
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [show (2 : ENNReal) ^ 256 = 2 ^ 64 * 2 ^ 192 by rw [← pow_add]]
        exact ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)

theorem compression_run_hits_slice192_bound (start : Nat) (hstart : start = 0 ∨ start = 64)
    (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget)
    (cache : CompressionCache) (targets : Finset (BitVec 192))
    (hclean : ¬ CacheHitsSlice192 start cache targets) :
    (prEvent ((fun res => CacheHitsSlice192 start res.2 targets) <$> (compressionRun permutation computation cache))) ≤
      (budget : ENNReal) * ((targets.card : ENNReal) / 2 ^ 192) := by
  classical
  induction computation using OracleComp.inductionOn generalizing budget cache with
  | pure value =>
    rw [compression_run_pure]
    simp only [prEvent_pure, hclean, ite_false]
    exact zero_le
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ ans, PublicQueryBound (next ans) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · rw [compression_run_private]
      apply prEvent_bind_le_of_forall_le_of_support
      intro ans _
      exact ih ans budget (by simpa only [Oracle.callCost, Nat.sub_zero] using bounded.2 ans) cache hclean
    · have hpos : 1 ≤ budget := bounded.1
      have htails := bounded.2
      have hmono : ((budget - 1 : Nat) : ENNReal) * ((targets.card : ENNReal) / 2 ^ 192) ≤
          (budget : ENNReal) * ((targets.card : ENNReal) / 2 ^ 192) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le budget 1)) zero_le
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress]
        cases hcached : cache input with
        | some ans =>
          exact (ih ans (budget - 1) (htails ans) cache hclean).trans hmono
        | none =>
          have hfresh : (prEvent ((fun ans : Digest => CacheHitsSlice192 start (cache.cacheQuery input ans) targets) <$>
              ($ᵗ CompressionSpec.Range input))) ≤ (targets.card : ENNReal) / 2 ^ 192 := by
            have hle : (prEvent ((fun ans : Digest => CacheHitsSlice192 start (cache.cacheQuery input ans) targets) <$>
                ($ᵗ CompressionSpec.Range input))) ≤
                (prEvent ((fun ans : Digest => ans.extractLsb' start 192 ∈ targets) <$> ($ᵗ Digest))) := by
              apply prEvent_mono_of_support
              intro ans _ ⟨k, v, hkv, hmem⟩
              by_cases hk : k = input
              · subst hk
                erw [QueryCache.cacheQuery_self cache k ans] at hkv
                cases hkv
                exact hmem
              · erw [QueryCache.cacheQuery_of_ne cache ans hk] at hkv
                exact (hclean ⟨k, v, hkv, hmem⟩).elim
            exact hle.trans (uniform_digest_hits_slice192_le start hstart targets)
          have hcont : ∀ ans ∈ support ($ᵗ CompressionSpec.Range input),
              ¬ CacheHitsSlice192 start (cache.cacheQuery input ans) targets →
              (prEvent ((fun res => CacheHitsSlice192 start res.2 targets) <$>
                (compressionRun permutation (next ans) (cache.cacheQuery input ans)))) ≤
                ((budget - 1 : Nat) : ENNReal) * ((targets.card : ENNReal) / 2 ^ 192) :=
            fun ans _ hsafe => ih ans (budget - 1) (htails ans) _ hsafe
          have hcomb := (prEvent_bind_le_prEvent_add_of_support
            ($ᵗ CompressionSpec.Range input)
            (fun ans => compressionRun permutation (next ans) (cache.cacheQuery input ans))
            (fun ans => CacheHitsSlice192 start (cache.cacheQuery input ans) targets)
            (fun res => CacheHitsSlice192 start res.2 targets) hcont).trans (add_le_add hfresh le_rfl)
          apply hcomb.trans_eq
          conv_rhs => rw [show budget = 1 + (budget - 1) by omega]
          push_cast; ring
      · rcases permQuery with input | input
        · rw [compression_run_permute]; exact (ih _ (budget - 1) (htails _) cache hclean).trans hmono
        · rw [compression_run_inverse]; exact (ih _ (budget - 1) (htails _) cache hclean).trans hmono

/-! ### 4. Pre-Salt Unsalted Leaf Calls (`queryAllUnsalted`, `3 * LENGTH` Queries) -/

def IDEAL_TREE_BUDGET : Nat := LENGTH + QUEUE_CALLS

theorem public_query_bound_pure' {α : Type} (x : α) (n : Nat) :
    PublicQueryBound (pure x : OracleComp World α) n := trivial

def queryCompress (h768 : COMPRESSION_INPUT_LENGTH = 768) (x : BitVec 768) :
    OracleComp World Digest :=
  (liftM (World.query (.inr (.inl (x.cast h768.symm)))) : OracleComp World Digest)

theorem queryCompress_bound (h768 : COMPRESSION_INPUT_LENGTH = 768) (x : BitVec 768) :
    PublicQueryBound (queryCompress h768 x) 1 :=
  ⟨Nat.le_refl 1, fun ans => public_query_bound_pure' (α := Digest) ans 0⟩

def oracleComp96 (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle) : Comp96 :=
  fun x => oracle.compression (x.cast h768.symm)

theorem queryCompress_fixed (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle) (x : BitVec 768) :
    fixedOracleRun oracle (queryCompress h768 x) = pure (oracleComp96 h768 oracle x) := by
  unfold queryCompress
  change fixedOracleRun oracle ((liftM (World.query (.inr (.inl (x.cast h768.symm)))) : OracleComp World Digest) >>= (pure : Digest → OracleComp World Digest)) = _
  rw [fixed_oracle_run_compress]
  exact fixed_oracle_run_pure oracle (α := Digest) (oracleComp96 h768 oracle x)

def queryUnsaltedLeaf (h768 : COMPRESSION_INPUT_LENGTH = 768) (val : Entry) :
    OracleComp World (Digest × Digest) := do
  let u ← queryCompress h768 (leafUInput val)
  let a ← queryCompress h768 (leafAInput u val)
  let b ← queryCompress h768 (leafBInput val)
  pure (a, b)

theorem queryUnsaltedLeaf_bound (h768 : COMPRESSION_INPUT_LENGTH = 768) (val : Entry) :
    PublicQueryBound (queryUnsaltedLeaf h768 val) 3 := by
  unfold queryUnsaltedLeaf
  exact public_query_bound_bind (first := 1) (second := 2) (queryCompress_bound h768 _) fun _ =>
    public_query_bound_bind (first := 1) (second := 1) (queryCompress_bound h768 _) fun _ =>
      public_query_bound_bind (first := 1) (second := 0) (queryCompress_bound h768 _) fun _ =>
        public_query_bound_pure' _ 0

theorem queryUnsaltedLeaf_fixed (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle) (val : Entry) :
    fixedOracleRun oracle (queryUnsaltedLeaf h768 val) =
      pure (leafA (oracleComp96 h768 oracle) val, leafB (oracleComp96 h768 oracle) val) := by
  unfold queryUnsaltedLeaf leafA leafB
  simp only [fixed_oracle_run_bind, queryCompress_fixed, pure_bind, fixed_oracle_run_pure]

def queryAllUnsaltedAux (h768 : COMPRESSION_INPUT_LENGTH = 768) (msg : Message) :
    Nat → OracleComp World ((Index → Digest) × (Index → Digest))
  | 0 => pure (fun _ => 0, fun _ => 0)
  | n + 1 => do
      let (aVec, bVec) ← queryAllUnsaltedAux h768 msg n
      if h : n < LENGTH then
        let i : Index := ⟨n, h⟩
        let (a, b) ← queryUnsaltedLeaf h768 (msg i)
        pure (Function.update aVec i a, Function.update bVec i b)
      else pure (aVec, bVec)

def queryAllUnsalted (h768 : COMPRESSION_INPUT_LENGTH = 768) (msg : Message) :
    OracleComp World ((Index → Digest) × (Index → Digest)) :=
  queryAllUnsaltedAux h768 msg LENGTH

private theorem queryAllUnsaltedAux_zero (h768 : COMPRESSION_INPUT_LENGTH = 768) (msg : Message) :
    queryAllUnsaltedAux h768 msg 0 = pure (fun _ => 0, fun _ => 0) := rfl

private theorem queryAllUnsaltedAux_succ (h768 : COMPRESSION_INPUT_LENGTH = 768) (msg : Message) (n : Nat) :
    queryAllUnsaltedAux h768 msg (n + 1) = (do
      let (aVec, bVec) ← queryAllUnsaltedAux h768 msg n
      if h : n < LENGTH then
        let i : Index := ⟨n, h⟩
        let (a, b) ← queryUnsaltedLeaf h768 (msg i)
        pure (Function.update aVec i a, Function.update bVec i b)
      else pure (aVec, bVec)) := rfl

attribute [irreducible] queryAllUnsaltedAux

theorem queryAllUnsalted_bound (h768 : COMPRESSION_INPUT_LENGTH = 768) (msg : Message) :
    PublicQueryBound (queryAllUnsalted h768 msg) (3 * LENGTH) := by
  have haux : ∀ n, PublicQueryBound (queryAllUnsaltedAux h768 msg n) (3 * n) := by
    intro n; induction n with
    | zero => rw [queryAllUnsaltedAux_zero]; exact public_query_bound_pure' _ _
    | succ n ih =>
      rw [queryAllUnsaltedAux_succ, show 3 * (n + 1) = 3 * n + 3 by omega]
      apply public_query_bound_bind ih
      rintro ⟨aVec, bVec⟩
      dsimp only
      by_cases hn : n < LENGTH
      · rw [dif_pos hn]
        simpa only [Nat.add_zero] using
          public_query_bound_bind (queryUnsaltedLeaf_bound h768 _) (fun _ => public_query_bound_pure' _ 0)
      · rw [dif_neg hn]
        exact (public_query_bound_pure' _ 0).mono (by omega)
  exact haux LENGTH

theorem queryAllUnsalted_fixed (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle) (msg : Message) :
    fixedOracleRun oracle (queryAllUnsalted h768 msg) =
      pure (fun i => leafA (oracleComp96 h768 oracle) (msg i),
            fun i => leafB (oracleComp96 h768 oracle) (msg i)) := by
  let c := oracleComp96 h768 oracle
  have haux : ∀ n, ∃ aVec bVec,
      fixedOracleRun oracle (queryAllUnsaltedAux h768 msg n) = pure (aVec, bVec) ∧
      ∀ i : Index, i.val < n → aVec i = leafA c (msg i) ∧ bVec i = leafB c (msg i) := by
    intro n; induction n with
    | zero =>
      rw [queryAllUnsaltedAux_zero]
      exact ⟨fun _ => 0, fun _ => 0, fixed_oracle_run_pure _ _, fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ n ih =>
      obtain ⟨aVec, bVec, hrun, hval⟩ := ih
      rw [queryAllUnsaltedAux_succ, fixed_oracle_run_bind, hrun, pure_bind]
      dsimp only
      by_cases hn : n < LENGTH
      · rw [dif_pos hn, fixed_oracle_run_bind, queryUnsaltedLeaf_fixed, pure_bind, fixed_oracle_run_pure]
        refine ⟨Function.update aVec ⟨n, hn⟩ (leafA c (msg ⟨n, hn⟩)),
                Function.update bVec ⟨n, hn⟩ (leafB c (msg ⟨n, hn⟩)), rfl, ?_⟩
        intro i hi
        by_cases heq : i = ⟨n, hn⟩
        · subst heq; simp
        · have hlt : i.val < n := by
            have : i.val ≠ n := fun h => heq (Fin.ext h)
            omega
          simp [Function.update_of_ne heq, hval i hlt]
      · rw [dif_neg hn, fixed_oracle_run_pure]
        exact ⟨aVec, bVec, rfl, fun i hi => hval i (by have := i.isLt; omega)⟩
  obtain ⟨aVec, bVec, hrun, hval⟩ := haux LENGTH
  have ha : aVec = fun i => leafA c (msg i) := funext fun i => (hval i i.isLt).1
  have hb : bVec = fun i => leafB c (msg i) := funext fun i => (hval i i.isLt).2
  unfold queryAllUnsalted
  rw [hrun, ha, hb]

private theorem compressionRun_queryCompress_mem (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (x : BitVec 768) (cache : CompressionCache)
    (res : Digest × CompressionCache)
    (hreach : res ∈ support (compressionRun permutation (queryCompress h768 x) cache)) :
    (∀ k v, cache k = some v → res.2 k = some v) ∧
    res.2 (x.cast h768.symm) = some res.1 := by
  have hcr := compression_run_compress permutation (x.cast h768.symm)
    (pure : BitVec COMPRESSION_OUTPUT_LENGTH → OracleComp World Digest) cache
  have hreach' : res ∈ support (compressionRun permutation
      ((liftM (World.query (.inr (.inl (x.cast h768.symm)))) : OracleComp World (BitVec COMPRESSION_OUTPUT_LENGTH)) >>=
        (pure : BitVec COMPRESSION_OUTPUT_LENGTH → OracleComp World Digest)) cache) := hreach
  rw [hcr] at hreach'
  cases hcached : cache (x.cast h768.symm) with
  | some ans =>
    rw [hcached] at hreach'
    dsimp only at hreach'
    rw [compression_run_pure] at hreach'
    erw [support_pure, Set.mem_singleton_iff] at hreach'
    subst res
    exact ⟨fun _ _ h => h, hcached⟩
  | none =>
    rw [hcached] at hreach'
    dsimp only at hreach'
    obtain ⟨ans, _, hreach'⟩ := (mem_support_bind_iff _ _ _).mp hreach'
    rw [compression_run_pure] at hreach'
    erw [support_pure, Set.mem_singleton_iff] at hreach'
    subst res
    refine ⟨?_, QueryCache.cacheQuery_self cache (x.cast h768.symm) ans⟩
    intro k v hkv
    by_cases hk : k = x.cast h768.symm
    · subst hk; rw [hcached] at hkv; cases hkv
    · erw [QueryCache.cacheQuery_of_ne cache ans hk]; exact hkv

/-- Every `((aVec, bVec), cache1)` in the support of `compressionRun perm (queryAllUnsalted msg) cache0`
caches all `3 * LENGTH` unsalted leaf calls, so EVERY extension `tableExtending cache1 table` agrees
with `(aVec, bVec)` on `leafA` and `leafB`! -/
theorem queryAllUnsalted_compressionRun_agrees (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (permutation : Perm) (msg : Message) (cache0 : CompressionCache)
    (res : ((Index → Digest) × (Index → Digest)) × CompressionCache)
    (hreach : res ∈ support (compressionRun permutation (queryAllUnsalted h768 msg) cache0)) :
    ∀ (table : Compression) (i : Index),
      let c : Comp96 := fun x => tableExtending res.2 table (x.cast h768.symm)
      leafA c (msg i) = res.1.1 i ∧ leafB c (msg i) = res.1.2 i := by
  have hleaf : ∀ (val : Entry) (cache : CompressionCache) (r : (Digest × Digest) × CompressionCache),
      r ∈ support (compressionRun permutation (queryUnsaltedLeaf h768 val) cache) →
      (∀ k v, cache k = some v → r.2 k = some v) ∧
      (∀ table : Compression,
        let c : Comp96 := fun x => tableExtending r.2 table (x.cast h768.symm)
        leafA c val = r.1.1 ∧ leafB c val = r.1.2) := by
    intro val cache r hr
    unfold queryUnsaltedLeaf at hr
    rw [compression_run_bind] at hr
    obtain ⟨⟨u, c1⟩, h1, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    dsimp only at hr
    rw [compression_run_bind] at hr
    obtain ⟨⟨a, c2⟩, h2, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    dsimp only at hr
    rw [compression_run_bind] at hr
    obtain ⟨⟨b, c3⟩, h3, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    dsimp only at hr
    rw [compression_run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    obtain ⟨hp1, hu⟩ := compressionRun_queryCompress_mem h768 permutation _ cache (u, c1) h1
    obtain ⟨hp2, ha⟩ := compressionRun_queryCompress_mem h768 permutation _ c1 (a, c2) h2
    obtain ⟨hp3, hb⟩ := compressionRun_queryCompress_mem h768 permutation _ c2 (b, c3) h3
    refine ⟨fun k v hkv => hp3 k v (hp2 k v (hp1 k v hkv)), fun table => ?_⟩
    have hu3 : c3 ((leafUInput val).cast h768.symm) = some u := hp3 _ _ (hp2 _ _ hu)
    have ha3 : c3 ((leafAInput u val).cast h768.symm) = some a := hp3 _ _ ha
    have hte : ∀ (x : BitVec 768) (d : Digest), c3 (x.cast h768.symm) = some d →
        (tableExtending c3 table (x.cast h768.symm) : Digest) = d := by
      intro x d hx; change (c3 _).getD _ = _; rw [hx]; rfl
    dsimp only [leafA, leafB]
    rw [hte _ _ hu3, hte _ _ ha3, hte _ _ hb]
    exact ⟨rfl, rfl⟩
  have haux : ∀ n (r : ((Index → Digest) × (Index → Digest)) × CompressionCache),
      r ∈ support (compressionRun permutation (queryAllUnsaltedAux h768 msg n) cache0) →
      ∀ (table : Compression) (i : Index), i.val < n →
        let c : Comp96 := fun x => tableExtending r.2 table (x.cast h768.symm)
        leafA c (msg i) = r.1.1 i ∧ leafB c (msg i) = r.1.2 i := by
    intro n; induction n with
    | zero => intro _ _ _ _ hi; exact (Nat.not_lt_zero _ hi).elim
    | succ n ih =>
      intro r hr
      rw [queryAllUnsaltedAux_succ, compression_run_bind] at hr
      obtain ⟨⟨⟨aV, bV⟩, cPrev⟩, hprev, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
      dsimp only at hr
      by_cases hn : n < LENGTH
      · rw [dif_pos hn, compression_run_bind] at hr
        obtain ⟨⟨⟨a, b⟩, cNext⟩, hleaf_r, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
        dsimp only at hr
        rw [compression_run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst r
        obtain ⟨hpres, hcur⟩ := hleaf (msg ⟨n, hn⟩) cPrev ((a, b), cNext) hleaf_r
        intro table i hi
        by_cases heq : i = ⟨n, hn⟩
        · subst heq; simp only [Function.update_self]; exact hcur table
        · have hlt : i.val < n := by have : i.val ≠ n := fun h => heq (Fin.ext h); omega
          simp only [Function.update_of_ne heq]
          have hfun : (fun x : BitVec 768 => (tableExtending cPrev (tableExtending cNext table) (x.cast h768.symm) : Digest)) =
              (fun x : BitVec 768 => (tableExtending cNext table (x.cast h768.symm) : Digest)) := by
            funext x
            cases hk : cPrev (x.cast h768.symm) with
            | none => change (cPrev _).getD _ = _; rw [hk]; rfl
            | some v =>
              have hv := hpres _ v hk
              change (cPrev _).getD _ = (cNext _).getD _; rw [hk, hv]; rfl
          have hih := ih ((aV, bV), cPrev) hprev (tableExtending cNext table) i hlt
          exact ⟨(congrArg (fun c : Comp96 => leafA c (msg i)) hfun).symm.trans hih.1,
                 (congrArg (fun c : Comp96 => leafB c (msg i)) hfun).symm.trans hih.2⟩
      · rw [dif_neg hn, compression_run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst r
        intro table i hi
        exact ih ((aV, bV), cPrev) hprev table i (by have := i.isLt; omega)
  intro table i
  exact haux LENGTH res hreach table i i.isLt


/-! ### 5. Bottom-Up Oracle Evaluation of the Pure 3-ary FIFO Queue Tree (`queryTreeFromLeafFn`) -/

def queryLevel0Aux (leafFn : Index → OracleComp World Digest) : Nat → OracleComp World (Nat → Digest)
  | 0 => pure (fun _ => 0)
  | n + 1 => do
      let prev ← queryLevel0Aux leafFn n
      if h : n < LENGTH then
        let d ← leafFn ⟨n, h⟩
        pure (Function.update prev n d)
      else pure prev

def queryQueueAux (h768 : COMPRESSION_INPUT_LENGTH = 768) (l0 : Nat → Digest) :
    Nat → OracleComp World (Nat → Digest)
  | 0 => pure l0
  | n + 1 => do
      let prev ← queryQueueAux h768 l0 n
      let d2 : Digest := if n = QUEUE_CALLS - 1 then 0 else prev (3 * n + 2)
      let d ← queryCompress h768 (ternaryInput (prev (3 * n)) (prev (3 * n + 1)) d2)
      pure (Function.update prev (LENGTH + n) d)

def queryTreeFromLeafFn (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (leafFn : Index → OracleComp World Digest) : OracleComp World (Nat → Digest) := do
  let l0 ← queryLevel0Aux leafFn LENGTH
  queryQueueAux h768 l0 QUEUE_CALLS

private theorem queryLevel0Aux_zero (leafFn : Index → OracleComp World Digest) :
    queryLevel0Aux leafFn 0 = pure (fun _ => 0) := rfl

private theorem queryLevel0Aux_succ (leafFn : Index → OracleComp World Digest) (n : Nat) :
    queryLevel0Aux leafFn (n + 1) = (do
      let prev ← queryLevel0Aux leafFn n
      if h : n < LENGTH then
        let d ← leafFn ⟨n, h⟩
        pure (Function.update prev n d)
      else pure prev) := rfl

private theorem queryQueueAux_zero (h768 : COMPRESSION_INPUT_LENGTH = 768) (l0 : Nat → Digest) :
    queryQueueAux h768 l0 0 = pure l0 := rfl

private theorem queryQueueAux_succ (h768 : COMPRESSION_INPUT_LENGTH = 768) (l0 : Nat → Digest) (n : Nat) :
    queryQueueAux h768 l0 (n + 1) = (do
      let prev ← queryQueueAux h768 l0 n
      let d2 : Digest := if n = QUEUE_CALLS - 1 then 0 else prev (3 * n + 2)
      let d ← queryCompress h768 (ternaryInput (prev (3 * n)) (prev (3 * n + 1)) d2)
      pure (Function.update prev (LENGTH + n) d)) := rfl

private theorem queryTreeFromLeafFn_def (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (leafFn : Index → OracleComp World Digest) :
    queryTreeFromLeafFn h768 leafFn = (do
      let l0 ← queryLevel0Aux leafFn LENGTH
      queryQueueAux h768 l0 QUEUE_CALLS) := rfl

attribute [irreducible] queryLevel0Aux queryQueueAux queryTreeFromLeafFn

theorem queryTreeFromLeafFn_bound_one (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (leafFn : Index → OracleComp World Digest)
    (hleaf : ∀ i, PublicQueryBound (leafFn i) 1) :
    PublicQueryBound (queryTreeFromLeafFn h768 leafFn) IDEAL_TREE_BUDGET := by
  have hl0 : ∀ n, PublicQueryBound (queryLevel0Aux leafFn n) n := by
    intro n; induction n with
    | zero => rw [queryLevel0Aux_zero]; exact public_query_bound_pure' _ _
    | succ n ih =>
      rw [queryLevel0Aux_succ]
      apply public_query_bound_bind ih
      intro prev
      split
      · simpa only [Nat.add_zero] using public_query_bound_bind (hleaf _) (fun _ => public_query_bound_pure' _ 0)
      · exact (public_query_bound_pure' prev 0).mono (by omega)
  have hq : ∀ l0 n, PublicQueryBound (queryQueueAux h768 l0 n) n := by
    intro l0 n; induction n with
    | zero => rw [queryQueueAux_zero]; exact public_query_bound_pure' _ _
    | succ n ih =>
      rw [queryQueueAux_succ]
      apply public_query_bound_bind ih
      intro _
      simpa only [Nat.add_zero] using public_query_bound_bind (queryCompress_bound h768 _) (fun _ => public_query_bound_pure' _ 0)
  rw [queryTreeFromLeafFn_def]
  exact public_query_bound_bind (hl0 LENGTH) fun l0 => hq l0 QUEUE_CALLS

theorem queryTreeFromLeafFn_fixed (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (leafFn : Index → OracleComp World Digest) (leaves : Index → Digest)
    (hleaf : ∀ i, fixedOracleRun oracle (leafFn i) = pure (leaves i)) :
    ∃ nodes,
      fixedOracleRun oracle (queryTreeFromLeafFn h768 leafFn) = pure nodes ∧
      ∀ v < TREE_NODES,
        nodes v = nodeValFromLeaves (fun x => oracle.compression (x.cast h768.symm)) leaves v := by
  let c : Comp96 := oracleComp96 h768 oracle
  have hLEN : LENGTH = 16777216 := by decide
  have hQC : QUEUE_CALLS = 8388608 := queueCalls_eq
  have hTN : TREE_NODES = 25165824 := treeNodes_eq
  have hRN : ROOT_NODE = 25165823 := rootNode_eq
  have hl0 : ∀ n, ∃ f, fixedOracleRun oracle (queryLevel0Aux leafFn n) = pure f ∧
      ∀ idx < n, idx < LENGTH → f idx = nodeValFromLeaves c leaves idx := by
    intro n; induction n with
    | zero =>
      rw [queryLevel0Aux_zero]
      exact ⟨fun _ => 0, fixed_oracle_run_pure _ _, fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ n ih =>
      obtain ⟨f, hrun, hval⟩ := ih
      rw [queryLevel0Aux_succ, fixed_oracle_run_bind, hrun, pure_bind]
      by_cases hn : n < LENGTH
      · rw [dif_pos hn, fixed_oracle_run_bind, hleaf ⟨n, hn⟩, pure_bind, fixed_oracle_run_pure]
        refine ⟨Function.update f n (leaves ⟨n, hn⟩), rfl, ?_⟩
        intro idx hlt hlen
        by_cases heq : idx = n
        · subst heq; rw [Function.update_self, nodeValFromLeaves_leaf c leaves idx hn]
        · rw [Function.update_of_ne heq]; exact hval idx (by omega) hlen
      · rw [dif_neg hn, fixed_oracle_run_pure]
        exact ⟨f, rfl, fun idx hlt hlen => hval idx (by omega) hlen⟩
  obtain ⟨l0, hl0_run, hl0_val⟩ := hl0 LENGTH
  have hq : ∀ n ≤ QUEUE_CALLS, ∃ f, fixedOracleRun oracle (queryQueueAux h768 l0 n) = pure f ∧
      ∀ v < LENGTH + n, f v = nodeValFromLeaves c leaves v := by
    intro n hn; induction n with
    | zero =>
      rw [queryQueueAux_zero]
      exact ⟨l0, fixed_oracle_run_pure _ _, fun v hv => hl0_val v (by omega) (by omega)⟩
    | succ n ih =>
      obtain ⟨f, hrun, hval⟩ := ih (by omega)
      rw [queryQueueAux_succ, fixed_oracle_run_bind, hrun, pure_bind, fixed_oracle_run_bind,
        queryCompress_fixed, pure_bind, fixed_oracle_run_pure]
      refine ⟨Function.update f (LENGTH + n) _, rfl, ?_⟩
      intro v hv
      by_cases heq : v = LENGTH + n
      · subst heq
        rw [Function.update_self]
        by_cases hlast : n = QUEUE_CALLS - 1
        · subst hlast
          have hrt_eq : LENGTH + (QUEUE_CALLS - 1) = ROOT_NODE := by omega
          rw [if_pos rfl, hrt_eq, nodeValFromLeaves_root]
          have h0 : f (3 * (QUEUE_CALLS - 1)) = nodeValFromLeaves c leaves 25165821 := by
            simpa only [show 3 * (QUEUE_CALLS - 1) = 25165821 by omega] using
              hval (3 * (QUEUE_CALLS - 1)) (by omega)
          have h1 : f (3 * (QUEUE_CALLS - 1) + 1) = nodeValFromLeaves c leaves 25165822 := by
            simpa only [show 3 * (QUEUE_CALLS - 1) + 1 = 25165822 by omega] using
              hval (3 * (QUEUE_CALLS - 1) + 1) (by omega)
          rw [h0, h1]
        · rw [if_neg hlast, nodeValFromLeaves_internal c leaves n (by omega)]
          have h0 := hval (3 * n) (by omega)
          have h1 := hval (3 * n + 1) (by omega)
          have h2 := hval (3 * n + 2) (by omega)
          rw [h0, h1, h2]
      · rw [Function.update_of_ne heq]
        exact hval v (by omega)
  obtain ⟨nodes, hq_run, hq_val⟩ := hq QUEUE_CALLS (le_refl _)
  rw [queryTreeFromLeafFn_def, fixed_oracle_run_bind, hl0_run, pure_bind, hq_run]
  exact ⟨nodes, rfl, fun v hv => hq_val v (by omega)⟩

/-! ### 6. Pure `GoodIdealTrace` Invariant for `queryTreeFromLeafFn (idealLeafFn ...)` -/

def GoodIdealQuery (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (aVec bVec : Index → Digest) (sOpen : Index → Salt192) (leafRand : Index → Digest)
    (positions : Positions) (trace : CompressionReplies) (x : BitVec COMPRESSION_INPUT_LENGTH) : Prop :=
  (∃ i ∈ positions, x = (leafFinalInput i (aVec i) (bVec i) (sOpen i)).cast h768.symm) ∨
  (((∃ i ∉ positions, x.extractLsb' 0 192 = (leafRand i).extractLsb' 0 192) ∨
    (∃ pair ∈ trace, x.extractLsb' 0 192 = pair.2.extractLsb' 0 192)) ∧
   (x.extractLsb' 576 192 = 0#192 ∨
    (∃ j ∉ positions, x.extractLsb' 576 192 = (leafRand j).extractLsb' 64 192) ∨
    (∃ pair ∈ trace, x.extractLsb' 576 192 = pair.2.extractLsb' 64 192)))

def GoodIdealTrace (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (aVec bVec : Index → Digest) (sOpen : Index → Salt192) (leafRand : Index → Digest)
    (positions : Positions) (trace : CompressionReplies) : Prop :=
  ∀ pair ∈ trace, GoodIdealQuery h768 aVec bVec sOpen leafRand positions trace pair.1

private theorem good_ideal_query_mono {h768 : COMPRESSION_INPUT_LENGTH = 768}
    {aVec bVec : Index → Digest} {sOpen : Index → Salt192} {leafRand : Index → Digest}
    {positions : Positions} {t1 t2 : CompressionReplies} (hsub : ∀ p ∈ t1, p ∈ t2) {x}
    (hg : GoodIdealQuery h768 aVec bVec sOpen leafRand positions t1 x) :
    GoodIdealQuery h768 aVec bVec sOpen leafRand positions t2 x := by
  rcases hg with hopen | ⟨hlo, hhi⟩
  · exact Or.inl hopen
  · refine Or.inr ⟨?_, ?_⟩
    · rcases hlo with h | ⟨p, hp, heq⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, hsub p hp, heq⟩
    · rcases hhi with h0 | h1 | ⟨p, hp, heq⟩
      · exact Or.inl h0
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr ⟨p, hsub p hp, heq⟩)

private theorem traceReplies_pure {α : Type} (v : α) :
    traceCompressionReplies (pure v : OracleComp World α) = pure (v, []) := rfl

private theorem traceReplies_bind {α β : Type} (comp : OracleComp World α)
    (next : α → OracleComp World β) :
    traceCompressionReplies (comp >>= next) = (do
      let p1 ← traceCompressionReplies comp
      let p2 ← traceCompressionReplies (next p1.1)
      pure (p2.1, p1.2 ++ p2.2)) := by
  induction comp using OracleComp.inductionOn with
  | pure v => simp [traceReplies_pure]
  | query_bind q k ih =>
    rcases q with coins | pq
    · change ((liftM (World.query (.inl coins)) : OracleComp World _) >>= fun ans =>
          traceCompressionReplies (k ans >>= next)) =
        (((liftM (World.query (.inl coins)) : OracleComp World _) >>= fun ans =>
          traceCompressionReplies (k ans)) >>= fun p1 =>
            traceCompressionReplies (next p1.1) >>= fun p2 => pure (p2.1, p1.2 ++ p2.2))
      rw [bind_assoc]
      exact bind_congr ih
    · rcases pq with inp | permq
      · change ((liftM (World.query (.inr (.inl inp))) : OracleComp World Digest) >>= fun (ans : Digest) =>
            traceCompressionReplies (k ans >>= next) >>= fun (v, tr) => pure (v, (inp, ans) :: tr)) =
          (((liftM (World.query (.inr (.inl inp))) : OracleComp World Digest) >>= fun (ans : Digest) =>
            traceCompressionReplies (k ans) >>= fun (v, tr) => pure (v, (inp, ans) :: tr)) >>=
              fun p1 => traceCompressionReplies (next p1.1) >>= fun p2 => pure (p2.1, p1.2 ++ p2.2))
        rw [bind_assoc]
        apply bind_congr; intro ans
        rw [ih ans, bind_assoc, bind_assoc]
        apply bind_congr; rintro ⟨a, t1⟩
        simp only [pure_bind, bind_assoc]
        apply bind_congr; rintro ⟨b, t2⟩
        simp only [pure_bind, List.cons_append]
      · change ((liftM (World.query (.inr (.inr permq))) : OracleComp World _) >>= fun ans =>
            traceCompressionReplies (k ans >>= next)) =
          (((liftM (World.query (.inr (.inr permq))) : OracleComp World _) >>= fun ans =>
            traceCompressionReplies (k ans)) >>= fun p1 =>
              traceCompressionReplies (next p1.1) >>= fun p2 => pure (p2.1, p1.2 ++ p2.2))
        rw [bind_assoc]
        exact bind_congr ih

private theorem traceReplies_queryCompress_fixed (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (x : BitVec 768) :
    fixedOracleRun oracle (traceCompressionReplies (queryCompress h768 x)) =
      (pure (oracle.compression (x.cast h768.symm),
        [(x.cast h768.symm, (oracle.compression (x.cast h768.symm) : Digest))]) :
        ProbComp (Digest × CompressionReplies)) := by
  unfold queryCompress
  change fixedOracleRun oracle ((liftM (World.query (.inr (.inl (x.cast h768.symm)))) : OracleComp World Digest) >>=
    fun (ans : Digest) => (pure (ans, ([] : CompressionReplies)) : OracleComp World (Digest × CompressionReplies)) >>=
      fun (v, tr) => pure (v, (x.cast h768.symm, ans) :: tr)) = _
  rw [fixed_oracle_run_compress, pure_bind]
  exact fixed_oracle_run_pure oracle (α := Digest × CompressionReplies) _

def idealLeafFn (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (aVec bVec : Index → Digest) (sOpen : Index → Salt192) (leafRand : Index → Digest)
    (positions : Positions) (i : Index) : OracleComp World Digest :=
  if i ∈ positions then
    queryCompress h768 (leafFinalInput i (aVec i) (bVec i) (sOpen i))
  else
    pure (leafRand i)

theorem idealLeafFn_bound (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (aVec bVec : Index → Digest) (sOpen : Index → Salt192) (leafRand : Index → Digest)
    (positions : Positions) (i : Index) :
    PublicQueryBound (idealLeafFn h768 aVec bVec sOpen leafRand positions i) 1 := by
  unfold idealLeafFn
  by_cases hi : i ∈ positions
  · rw [if_pos hi]; exact queryCompress_bound h768 _
  · rw [if_neg hi]; exact public_query_bound_pure' _ _

/-- Every compression query executed during `queryTreeFromLeafFn (idealLeafFn ...)` satisfies
`GoodIdealTrace`: it is either an opened leaf Call-3 or an internal queue node whose low 192 bits
come from `leafRand` or an earlier reply and whose high 192 bits are either `0#192` (at the root),
`(leafRand j)[64..256)`, or an earlier reply's `[64..256)`. -/
theorem queryIdealTree_good_trace (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (aVec bVec : Index → Digest) (sOpen : Index → Salt192)
    (leafRand : Index → Digest) (positions : Positions) :
    ∃ nodes trace,
      fixedOracleRun oracle (traceCompressionReplies
        (queryTreeFromLeafFn h768 (idealLeafFn h768 aVec bVec sOpen leafRand positions))) = pure (nodes, trace) ∧
      GoodIdealTrace h768 aVec bVec sOpen leafRand positions trace := by
  have hLEN : LENGTH = 16777216 := by decide
  have hQC : QUEUE_CALLS = 8388608 := queueCalls_eq
  have hcast0 : ∀ (x : BitVec 768), (x.cast h768.symm).extractLsb' 0 192 = x.extractLsb' 0 192 :=
    fun x => extractLsb'_cast_eq h768.symm x 0 192
  have hcast576 : ∀ (x : BitVec 768), (x.cast h768.symm).extractLsb' 576 192 = x.extractLsb' 576 192 :=
    fun x => extractLsb'_cast_eq h768.symm x 576 192
  have hleaf : ∀ i : Index, ∃ d tr,
      fixedOracleRun oracle (traceCompressionReplies (idealLeafFn h768 aVec bVec sOpen leafRand positions i)) = pure (d, tr) ∧
      GoodIdealTrace h768 aVec bVec sOpen leafRand positions tr ∧
      ((∃ k ∉ positions, d = leafRand k) ∨ (∃ p ∈ tr, d = p.2)) := by
    intro i
    unfold idealLeafFn
    by_cases hi : i ∈ positions
    · rw [if_pos hi]
      let x := (leafFinalInput i (aVec i) (bVec i) (sOpen i)).cast h768.symm
      let d : Digest := oracle.compression x
      refine ⟨d, [(x, d)], traceReplies_queryCompress_fixed h768 oracle _, ?_, Or.inr ⟨(x, d), by simp, rfl⟩⟩
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact Or.inl ⟨i, hi, rfl⟩
    · rw [if_neg hi]
      exact ⟨leafRand i, [], by simp only [traceReplies_pure, fixed_oracle_run_pure],
        by simp [GoodIdealTrace], Or.inl ⟨i, hi, rfl⟩⟩
  have hl0 : ∀ n, ∃ f tr,
      fixedOracleRun oracle (traceCompressionReplies (queryLevel0Aux (idealLeafFn h768 aVec bVec sOpen leafRand positions) n)) = pure (f, tr) ∧
      GoodIdealTrace h768 aVec bVec sOpen leafRand positions tr ∧
      ∀ idx < n, idx < LENGTH → ((∃ k ∉ positions, f idx = leafRand k) ∨ (∃ p ∈ tr, f idx = p.2)) := by
    intro n; induction n with
    | zero =>
      exact ⟨fun _ => 0, [], by simp only [queryLevel0Aux_zero, traceReplies_pure, fixed_oracle_run_pure],
        by simp [GoodIdealTrace], fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ n ih =>
      obtain ⟨f, tr, hrun, hgood, hnodes⟩ := ih
      rw [queryLevel0Aux_succ, traceReplies_bind, fixed_oracle_run_bind, hrun, pure_bind]
      dsimp only
      by_cases hn : n < LENGTH
      · rw [dif_pos hn]
        obtain ⟨d, trd, hdrun, hdgood, hdp⟩ := hleaf ⟨n, hn⟩
        simp only [traceReplies_bind, traceReplies_pure, fixed_oracle_run_bind, fixed_oracle_run_pure,
          hdrun, pure_bind, List.append_nil]
        refine ⟨Function.update f n d, tr ++ trd, rfl, ?_, ?_⟩
        · intro p hp
          rcases List.mem_append.mp hp with hp1 | hp2
          · exact good_ideal_query_mono (fun q hq => List.mem_append_left _ hq) (hgood p hp1)
          · exact good_ideal_query_mono (fun q hq => List.mem_append_right _ hq) (hdgood p hp2)
        · intro idx hlt hlen
          by_cases heq : idx = n
          · subst heq; rw [Function.update_self]
            rcases hdp with hlr | ⟨p, hp, hpeq⟩
            · exact Or.inl hlr
            · exact Or.inr ⟨p, List.mem_append_right _ hp, hpeq⟩
          · rw [Function.update_of_ne heq]
            rcases hnodes idx (by omega) hlen with hlr | ⟨p, hp, hpeq⟩
            · exact Or.inl hlr
            · exact Or.inr ⟨p, List.mem_append_left _ hp, hpeq⟩
      · rw [dif_neg hn]
        simp only [traceReplies_pure, fixed_oracle_run_pure, pure_bind, List.append_nil]
        exact ⟨f, tr, rfl, hgood, fun idx hlt hlen => hnodes idx (by omega) hlen⟩
  obtain ⟨l0, tr0, htr0_run, htr0_good, htr0_nodes⟩ := hl0 LENGTH
  have hq : ∀ n ≤ QUEUE_CALLS, ∃ f tr,
      fixedOracleRun oracle (traceCompressionReplies (queryQueueAux h768 l0 n)) = pure (f, tr) ∧
      GoodIdealTrace h768 aVec bVec sOpen leafRand positions (tr0 ++ tr) ∧
      ∀ v < LENGTH + n, (∃ k ∉ positions, f v = leafRand k) ∨ (∃ p ∈ tr0 ++ tr, f v = p.2) := by
    intro n hn; induction n with
    | zero =>
      refine ⟨l0, [], by simp only [queryQueueAux_zero, traceReplies_pure, fixed_oracle_run_pure],
        by simpa using htr0_good, fun v hv => by
          simpa using htr0_nodes v (by omega) (by omega)⟩
    | succ n ih =>
      obtain ⟨f, tr, hrun, hgood, hnodes⟩ := ih (by omega)
      rw [queryQueueAux_succ]
      let d2 : Digest := if n = QUEUE_CALLS - 1 then 0 else f (3 * n + 2)
      let x := (ternaryInput (f (3 * n)) (f (3 * n + 1)) d2).cast h768.symm
      let d : Digest := oracle.compression x
      have hrun1 :
          fixedOracleRun oracle (traceCompressionReplies (do
            let prev ← queryQueueAux h768 l0 n
            let d2' : Digest := if n = QUEUE_CALLS - 1 then 0 else prev (3 * n + 2)
            let d' ← queryCompress h768 (ternaryInput (prev (3 * n)) (prev (3 * n + 1)) d2')
            pure (Function.update prev (LENGTH + n) d'))) =
          pure (Function.update f (LENGTH + n) d, tr ++ [(x, d)]) := by
        simp only [traceReplies_bind, traceReplies_pure, fixed_oracle_run_bind, fixed_oracle_run_pure,
          traceReplies_queryCompress_fixed, hrun, pure_bind, List.append_nil]
        rfl
      refine ⟨Function.update f (LENGTH + n) d, tr ++ [(x, d)], hrun1, ?_, ?_⟩
      · intro p hp
        have hmem_sub : ∀ q ∈ tr0 ++ tr, q ∈ tr0 ++ (tr ++ [(x, d)]) := by
          intro q hq
          rcases List.mem_append.mp hq with h1 | h2
          · exact List.mem_append_left _ h1
          · exact List.mem_append_right _ (List.mem_append_left _ h2)
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with h1 | (h2 | rfl)
        · exact good_ideal_query_mono hmem_sub (hgood p (List.mem_append_left _ h1))
        · exact good_ideal_query_mono hmem_sub (hgood p (List.mem_append_right _ h2))
        · right
          constructor
          · rcases hnodes (3 * n) (by omega) with ⟨k, hk, heq⟩ | ⟨q, hq, heq⟩
            · left; refine ⟨k, hk, ?_⟩
              dsimp only [x]; rw [hcast0]; unfold ternaryInput; rw [extractLsb'_0_192_append_digest, heq]
            · right; refine ⟨q, hmem_sub q hq, ?_⟩
              dsimp only [x]; rw [hcast0]; unfold ternaryInput; rw [extractLsb'_0_192_append_digest, heq]
          · by_cases hlast : n = QUEUE_CALLS - 1
            · left
              dsimp only [x, d2]
              rw [if_pos hlast, hcast576, extractLsb'_576_192_ternary_zero]
            · rcases hnodes (3 * n + 2) (by omega) with ⟨k, hk, heq⟩ | ⟨q, hq, heq⟩
              · right; left; refine ⟨k, hk, ?_⟩
                dsimp only [x, d2]; rw [if_neg hlast, hcast576, extractLsb'_576_192_ternary, heq]
              · right; right; refine ⟨q, hmem_sub q hq, ?_⟩
                dsimp only [x, d2]; rw [if_neg hlast, hcast576, extractLsb'_576_192_ternary, heq]
      · intro v hv
        by_cases heq : v = LENGTH + n
        · subst heq; rw [Function.update_self]; exact Or.inr ⟨(x, d), by simp, rfl⟩
        · rw [Function.update_of_ne heq]
          rcases hnodes v (by omega) with hlr | ⟨p, hp, hpeq⟩
          · exact Or.inl hlr
          · refine Or.inr ⟨p, ?_, hpeq⟩
            rcases List.mem_append.mp hp with h1 | h2
            · exact List.mem_append_left _ h1
            · exact List.mem_append_right _ (List.mem_append_left _ h2)
  obtain ⟨nodes, trQ, hq_run, hq_good, _⟩ := hq QUEUE_CALLS (le_refl _)
  rw [queryTreeFromLeafFn_def]
  simp only [traceReplies_bind, fixed_oracle_run_bind, fixed_oracle_run_pure,
    htr0_run, hq_run, pure_bind]
  exact ⟨nodes, tr0 ++ trQ, rfl, hq_good⟩

end CommitGolfCandidate
