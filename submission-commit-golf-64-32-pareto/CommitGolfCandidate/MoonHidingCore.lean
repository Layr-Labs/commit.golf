import CommitGolfCandidate.MoonBinding
import CommitGolfCandidate.HidingTrace
import Mathlib.Data.Fintype.EquivFin

/-! Core probabilistic, ROM-caching, and bottom-up binary-tree-query primitives for our
paired late-salt (SM-PLS-40) statistical hiding proof on the 64-32 `C0 -> P1 -> C2 -> C3` scheme:
- `splitBlocks` & `combinePairRand`: bijection between bulk RANDOM(40) bits and `(sL, sM, sR)`
- `mergePairRand`: exact split of `(sL, sM, sR)` into opened coordinates + secret `(sL_hid, sR_hid)`
- Lazy-ROM `low238` hit bounds (`CacheHits238`)
- `queryAllUnsalted` (`3 * LENGTH` unsalted leaf calls `C0, P1, C2`) cached prior to salt sampling
- `queryTreeFromLeafFn` (pure binary tree) and its deterministic `GoodIdealTrace` invariant. -/
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

/-! ### 2. Stage-1 Lazy Sampling, Cache Coverage, and Compression-Reply Tracing -/

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

abbrev CompressionReplies := List (BitVec COMPRESSION_INPUT_LENGTH × Digest)

def traceCompressionReplies {α : Type} (computation : OracleComp World α) :
    OracleComp World (α × CompressionReplies) :=
  OracleComp.recOn computation
    (fun value => pure (value, []))
    (fun query _ next =>
      match query, next with
      | .inr (.inl input), next => do
          let answer ← (liftM (World.query (.inr (.inl input))) : OracleComp World _)
          let (value, trace) ← next answer
          pure (value, (input, answer) :: trace)
      | q, next => do
          let answer ← (liftM (World.query q) : OracleComp World _)
          next answer)

theorem public_query_bound_pure' {α : Type} (x : α) (n : Nat) :
    PublicQueryBound (pure x : OracleComp World α) n := trivial

theorem traceReplies_bound {α : Type} (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget) :
    PublicQueryBound (traceCompressionReplies computation) budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure _ => exact public_query_bound_pure' _ _
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | publicQuery
    · exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩
    · rcases publicQuery with input | permQuery
      · refine ⟨bounded.1, fun answer => ?_⟩
        have htail := ih answer (budget - 1) (bounded.2 answer)
        refine (public_query_bound_bind (second := 0) htail
          (fun p => public_query_bound_pure' (p.1, (input, answer) :: p.2) 0)).mono ?_
        change budget - 1 + 0 ≤ budget - 1
        omega
      · exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩

theorem traceReplies_compressionRun_cache (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (cache : CompressionCache)
    (result : (α × CompressionReplies) × CompressionCache)
    (reached : result ∈ support (compressionRun permutation (traceCompressionReplies computation) cache)) :
    (∀ k v, cache k = some v → result.2 k = some v) ∧
    (∀ pair ∈ result.1.2, result.2 pair.1 = some pair.2) := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
    change result ∈ support (compressionRun permutation (pure (value, [])) cache) at reached
    rw [compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact ⟨fun _ _ h => h, by simp⟩
  | query_bind query next ih =>
    rcases query with coins | publicQuery
    · change result ∈ support (compressionRun permutation
        ((liftM (World.query (.inl coins)) : OracleComp World _) >>= fun answer =>
          traceCompressionReplies (next answer)) cache) at reached
      rw [compression_run_private] at reached
      obtain ⟨answer, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
      exact ih answer cache result reached
    · rcases publicQuery with input | permQuery
      · change result ∈ support (compressionRun permutation
          ((liftM (World.query (.inr (.inl input))) : OracleComp World _) >>= fun answer =>
            traceCompressionReplies (next answer) >>= fun (value, trace) =>
              pure (value, (input, answer) :: trace)) cache) at reached
        rw [compression_run_compress] at reached
        cases hcached : cache input with
        | some answer =>
          rw [hcached] at reached
          dsimp only at reached
          rw [compression_run_bind] at reached
          obtain ⟨⟨⟨v, tr⟩, c'⟩, hreach, hrest⟩ := (mem_support_bind_iff _ _ _).mp reached
          dsimp only at hrest
          rw [compression_run_pure] at hrest
          erw [support_pure, Set.mem_singleton_iff] at hrest
          subst result
          obtain ⟨hpres, hmem⟩ := ih answer cache ((v, tr), c') hreach
          refine ⟨hpres, ?_⟩
          intro pair hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hpres input answer hcached
          · exact hmem pair hp
        | none =>
          rw [hcached] at reached
          dsimp only at reached
          obtain ⟨answer, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
          rw [compression_run_bind] at reached
          obtain ⟨⟨⟨v, tr⟩, c'⟩, hreach, hrest⟩ := (mem_support_bind_iff _ _ _).mp reached
          dsimp only at hrest
          rw [compression_run_pure] at hrest
          erw [support_pure, Set.mem_singleton_iff] at hrest
          subst result
          obtain ⟨hpres, hmem⟩ := ih answer (cache.cacheQuery input answer) ((v, tr), c') hreach
          refine ⟨?_, ?_⟩
          · intro k v' hkv
            apply hpres
            by_cases hk : k = input
            · subst hk; rw [hcached] at hkv; cases hkv
            · erw [QueryCache.cacheQuery_of_ne cache answer hk]; exact hkv
          · intro pair hp
            rcases List.mem_cons.mp hp with rfl | hp
            · exact hpres input answer (QueryCache.cacheQuery_self cache input answer)
            · exact hmem pair hp
      · rcases permQuery with input | input
        · change result ∈ support (compressionRun permutation
            ((liftM (World.query (.inr (.inr (.inl input)))) : OracleComp World _) >>= fun answer =>
              traceCompressionReplies (next answer)) cache) at reached
          rw [compression_run_permute] at reached
          exact ih _ cache result reached
        · change result ∈ support (compressionRun permutation
            ((liftM (World.query (.inr (.inr (.inr input)))) : OracleComp World _) >>= fun answer =>
              traceCompressionReplies (next answer)) cache) at reached
          rw [compression_run_inverse] at reached
          exact ih _ cache result reached

/-! ### 3. BitVec Helpers & Lazy-ROM `low238` Hit Bounds -/

theorem extractLsb'_cast_eq {m n : Nat} (h : m = n) (x : BitVec m) (start len : Nat) :
    (x.cast h).extractLsb' start len = x.extractLsb' start len := by
  subst h; rfl

theorem fixed_oracle_run_compress (oracle : Oracle) {α : Type}
    (x : BitVec COMPRESSION_INPUT_LENGTH) (next : Digest → OracleComp World α) :
    fixedOracleRun oracle ((liftM (World.query (.inr (.inl x))) : OracleComp World Digest) >>= next) =
      fixedOracleRun oracle (next (oracle.compression x)) :=
  fixed_oracle_run_public oracle (.inl x) next

theorem fixed_oracle_run_permute (oracle : Oracle) {α : Type}
    (x : BitVec PERMUTATION_WIDTH) (next : BitVec PERMUTATION_WIDTH → OracleComp World α) :
    fixedOracleRun oracle ((liftM (World.query (.inr (.inr (.inl x)))) : OracleComp World (BitVec PERMUTATION_WIDTH)) >>= next) =
      fixedOracleRun oracle (next (oracle.permutation x)) :=
  fixed_oracle_run_public oracle (.inr (.inl x)) next

def CacheHits238 (cache : CompressionCache) (targets : Finset (BitVec 238)) : Prop :=
  ∃ (k : BitVec COMPRESSION_INPUT_LENGTH) (ans : Digest),
    cache k = some ans ∧ low238 ans ∈ targets

private theorem card_low238_preimage_hiding (targets : Finset (BitVec 238))
    [DecidablePred (fun ans : Digest => low238 ans ∈ targets)] :
    (Finset.univ.filter (fun ans : Digest => low238 ans ∈ targets)).card ≤ 2 ^ 18 * targets.card := by
  have hinj : Set.InjOn (fun ans : Digest => (ans.extractLsb' 238 18, low238 ans))
      (Finset.univ.filter (fun ans : Digest => low238 ans ∈ targets) : Set Digest) := by
    intro a _ b _ h
    have hhi : a.extractLsb' 238 18 = b.extractLsb' 238 18 := congrArg Prod.fst h
    have hlo : low238 a = low238 b := congrArg Prod.snd h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    by_cases h238 : i < 238
    · have := congrArg (fun v : BitVec 238 => v.getLsbD i) hlo
      simpa only [low238, BitVec.getLsbD_extractLsb', h238, decide_true, Bool.true_and, Nat.zero_add] using this
    · have hi18 : i - 238 < 18 := by omega
      have := congrArg (fun v : BitVec 18 => v.getLsbD (i - 238)) hhi
      simpa only [BitVec.getLsbD_extractLsb', hi18, decide_true, Bool.true_and,
        show 238 + (i - 238) = i by omega] using this
  have hmaps : Set.MapsTo (fun ans : Digest => (ans.extractLsb' 238 18, low238 ans))
      (Finset.univ.filter (fun ans : Digest => low238 ans ∈ targets) : Set Digest)
      ((Finset.univ ×ˢ targets : Finset (BitVec 18 × BitVec 238)) : Set (BitVec 18 × BitVec 238)) := by
    intro ans hans
    rw [Finset.mem_coe, Finset.mem_filter] at hans
    rw [Finset.mem_coe, Finset.mem_product]
    exact ⟨Finset.mem_univ _, hans.2⟩
  calc
    (Finset.univ.filter (fun ans : Digest => low238 ans ∈ targets)).card
      ≤ (Finset.univ ×ˢ targets : Finset (BitVec 18 × BitVec 238)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = (Finset.univ : Finset (BitVec 18)).card * targets.card := Finset.card_product _ _
    _ = 2 ^ 18 * targets.card := by rw [Finset.card_univ, Fintype.card_bitVec]

theorem uniform_digest_hits_238_le (targets : Finset (BitVec 238)) :
    (prEvent ((fun ans : Digest => low238 ans ∈ targets) <$> ($ᵗ Digest))) ≤
      (targets.card : ENNReal) / 2 ^ 238 := by
  classical
  rw [SampleableType.prEvent_uniformSample]
  have hcard : Fintype.card Digest = 2 ^ 256 := Fintype.card_bitVec 256
  rw [hcard]
  calc
    ((Finset.univ.filter (fun ans : Digest => low238 ans ∈ targets)).card : ENNReal) / (2 ^ 256 : Nat)
      ≤ ((2 ^ 18 * targets.card : Nat) : ENNReal) / (2 ^ 256 : Nat) :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr (card_low238_preimage_hiding targets)) _
    _ = (targets.card : ENNReal) / 2 ^ 238 := by
        simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [show (2 : ENNReal) ^ 256 = 2 ^ 18 * 2 ^ 238 by rw [← pow_add]]
        exact ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)

theorem compression_run_hits_238_bound (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound computation budget)
    (cache : CompressionCache) (targets : Finset (BitVec 238))
    (hclean : ¬ CacheHits238 cache targets) :
    (prEvent ((fun res => CacheHits238 res.2 targets) <$> (compressionRun permutation computation cache))) ≤
      (budget : ENNReal) * ((targets.card : ENNReal) / 2 ^ 238) := by
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
      have hmono : ((budget - 1 : Nat) : ENNReal) * ((targets.card : ENNReal) / 2 ^ 238) ≤
          (budget : ENNReal) * ((targets.card : ENNReal) / 2 ^ 238) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le budget 1)) zero_le
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress]
        cases hcached : cache input with
        | some ans =>
          exact (ih ans (budget - 1) (htails ans) cache hclean).trans hmono
        | none =>
          have hfresh : (prEvent ((fun ans : Digest => CacheHits238 (cache.cacheQuery input ans) targets) <$>
              ($ᵗ CompressionSpec.Range input))) ≤ (targets.card : ENNReal) / 2 ^ 238 := by
            have hle : (prEvent ((fun ans : Digest => CacheHits238 (cache.cacheQuery input ans) targets) <$>
                ($ᵗ CompressionSpec.Range input))) ≤
                (prEvent ((fun ans : Digest => low238 ans ∈ targets) <$> ($ᵗ Digest))) := by
              apply prEvent_mono_of_support
              intro ans _ ⟨k, v, hkv, hmem⟩
              by_cases hk : k = input
              · subst hk
                erw [QueryCache.cacheQuery_self cache k ans] at hkv
                cases hkv
                exact hmem
              · erw [QueryCache.cacheQuery_of_ne cache ans hk] at hkv
                exact (hclean ⟨k, v, hkv, hmem⟩).elim
            exact hle.trans (uniform_digest_hits_238_le targets)
          have hcont : ∀ ans ∈ support ($ᵗ CompressionSpec.Range input),
              ¬ CacheHits238 (cache.cacheQuery input ans) targets →
              (prEvent ((fun res => CacheHits238 res.2 targets) <$>
                (compressionRun permutation (next ans) (cache.cacheQuery input ans)))) ≤
                ((budget - 1 : Nat) : ENNReal) * ((targets.card : ENNReal) / 2 ^ 238) :=
            fun ans _ hsafe => ih ans (budget - 1) (htails ans) _ hsafe
          have hcomb := (prEvent_bind_le_prEvent_add_of_support
            ($ᵗ CompressionSpec.Range input)
            (fun ans => compressionRun permutation (next ans) (cache.cacheQuery input ans))
            (fun ans => CacheHits238 (cache.cacheQuery input ans) targets)
            (fun res => CacheHits238 res.2 targets) hcont).trans (add_le_add hfresh le_rfl)
          apply hcomb.trans_eq
          conv_rhs => rw [show budget = 1 + (budget - 1) by omega]
          push_cast; ring
      · rcases permQuery with input | input
        · rw [compression_run_permute]; exact (ih _ (budget - 1) (htails _) cache hclean).trans hmono
        · rw [compression_run_inverse]; exact (ih _ (budget - 1) (htails _) cache hclean).trans hmono

/-! ### 4. Pre-Salt Unsalted Leaf Calls (`queryAllUnsalted`, `3 * LENGTH` Queries: `C0, P1, C2`) -/

def IDEAL_TREE_BUDGET : Nat := LENGTH + (LENGTH - 1)

def queryCompress (h512 : COMPRESSION_INPUT_LENGTH = 512) (x : BitVec 512) :
    OracleComp World Digest :=
  (liftM (World.query (.inr (.inl (x.cast h512.symm)))) : OracleComp World Digest)

def queryPermute (x : BitVec PERMUTATION_WIDTH) : OracleComp World (BitVec PERMUTATION_WIDTH) :=
  (liftM (World.query (.inr (.inr (.inl x)))) : OracleComp World (BitVec PERMUTATION_WIDTH))

theorem queryCompress_bound (h512 : COMPRESSION_INPUT_LENGTH = 512) (x : BitVec 512) :
    PublicQueryBound (queryCompress h512 x) 1 :=
  ⟨Nat.le_refl 1, fun ans => public_query_bound_pure' (α := Digest) ans 0⟩

theorem queryPermute_bound (x : BitVec PERMUTATION_WIDTH) :
    PublicQueryBound (queryPermute x) 1 :=
  ⟨Nat.le_refl 1, fun ans => public_query_bound_pure' (α := BitVec PERMUTATION_WIDTH) ans 0⟩

def oracleComp64 (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle) : Comp64 :=
  fun x => oracle.compression (x.cast h512.symm)

theorem queryCompress_fixed (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle) (x : BitVec 512) :
    fixedOracleRun oracle (queryCompress h512 x) = pure (oracleComp64 h512 oracle x) := by
  unfold queryCompress
  change fixedOracleRun oracle ((liftM (World.query (.inr (.inl (x.cast h512.symm)))) : OracleComp World Digest) >>= (pure : Digest → OracleComp World Digest)) = _
  rw [fixed_oracle_run_compress]
  exact fixed_oracle_run_pure oracle (α := Digest) (oracleComp64 h512 oracle x)

theorem queryPermute_fixed (oracle : Oracle) (x : BitVec PERMUTATION_WIDTH) :
    fixedOracleRun oracle (queryPermute x) = pure (oracle.permutation x) := by
  unfold queryPermute
  change fixedOracleRun oracle ((liftM (World.query (.inr (.inr (.inl x)))) : OracleComp World (BitVec PERMUTATION_WIDTH)) >>= (pure : BitVec PERMUTATION_WIDTH → OracleComp World (BitVec PERMUTATION_WIDTH))) = _
  rw [fixed_oracle_run_permute]
  exact fixed_oracle_run_pure oracle (α := BitVec PERMUTATION_WIDTH) (oracle.permutation x)

def queryUnsaltedLeaf (h512 : COMPRESSION_INPUT_LENGTH = 512) (val : Entry) :
    OracleComp World Digest := do
  let c0 ← queryCompress h512 (leafC0Input val)
  let y ← queryPermute (leafP1Input c0 val)
  queryCompress h512 (leafC2Input y val)

theorem queryUnsaltedLeaf_bound (h512 : COMPRESSION_INPUT_LENGTH = 512) (val : Entry) :
    PublicQueryBound (queryUnsaltedLeaf h512 val) 3 := by
  unfold queryUnsaltedLeaf
  exact public_query_bound_bind (first := 1) (second := 2) (queryCompress_bound h512 _) fun _ =>
    public_query_bound_bind (first := 1) (second := 1) (queryPermute_bound _) fun _ =>
      queryCompress_bound h512 _

theorem queryUnsaltedLeaf_fixed (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle) (val : Entry) :
    fixedOracleRun oracle (queryUnsaltedLeaf h512 val) =
      pure (leafA (oracleComp64 h512 oracle) oracle.permutation val) := by
  unfold queryUnsaltedLeaf leafA
  rw [fixed_oracle_run_bind, queryCompress_fixed, pure_bind, fixed_oracle_run_bind]
  erw [queryPermute_fixed]
  rw [pure_bind, queryCompress_fixed]

def queryAllUnsaltedAux (h512 : COMPRESSION_INPUT_LENGTH = 512) (msg : Message) :
    Nat → OracleComp World (Index → Digest)
  | 0 => pure (fun _ => 0)
  | n + 1 => do
      let aVec ← queryAllUnsaltedAux h512 msg n
      if h : n < LENGTH then
        let i : Index := ⟨n, h⟩
        let a ← queryUnsaltedLeaf h512 (msg i)
        pure (Function.update aVec i a)
      else pure aVec

def queryAllUnsalted (h512 : COMPRESSION_INPUT_LENGTH = 512) (msg : Message) :
    OracleComp World (Index → Digest) :=
  queryAllUnsaltedAux h512 msg LENGTH

private theorem queryAllUnsaltedAux_zero (h512 : COMPRESSION_INPUT_LENGTH = 512) (msg : Message) :
    queryAllUnsaltedAux h512 msg 0 = pure (fun _ => 0) := rfl

private theorem queryAllUnsaltedAux_succ (h512 : COMPRESSION_INPUT_LENGTH = 512) (msg : Message) (n : Nat) :
    queryAllUnsaltedAux h512 msg (n + 1) = (do
      let aVec ← queryAllUnsaltedAux h512 msg n
      if h : n < LENGTH then
        let i : Index := ⟨n, h⟩
        let a ← queryUnsaltedLeaf h512 (msg i)
        pure (Function.update aVec i a)
      else pure aVec) := rfl

attribute [irreducible] queryAllUnsaltedAux

theorem queryAllUnsalted_bound (h512 : COMPRESSION_INPUT_LENGTH = 512) (msg : Message) :
    PublicQueryBound (queryAllUnsalted h512 msg) (3 * LENGTH) := by
  have haux : ∀ n, PublicQueryBound (queryAllUnsaltedAux h512 msg n) (3 * n) := by
    intro n; induction n with
    | zero => rw [queryAllUnsaltedAux_zero]; exact public_query_bound_pure' _ _
    | succ n ih =>
      rw [queryAllUnsaltedAux_succ, show 3 * (n + 1) = 3 * n + 3 by omega]
      apply public_query_bound_bind ih
      intro aVec
      dsimp only
      by_cases hn : n < LENGTH
      · rw [dif_pos hn]
        simpa only [Nat.add_zero] using
          public_query_bound_bind (queryUnsaltedLeaf_bound h512 _) (fun _ => public_query_bound_pure' _ 0)
      · rw [dif_neg hn]
        exact (public_query_bound_pure' _ 0).mono (by omega)
  exact haux LENGTH

theorem queryAllUnsalted_fixed (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle) (msg : Message) :
    fixedOracleRun oracle (queryAllUnsalted h512 msg) =
      pure (fun i => leafA (oracleComp64 h512 oracle) oracle.permutation (msg i)) := by
  let c := oracleComp64 h512 oracle
  have haux : ∀ n, ∃ aVec,
      fixedOracleRun oracle (queryAllUnsaltedAux h512 msg n) = pure aVec ∧
      ∀ i : Index, i.val < n → aVec i = leafA c oracle.permutation (msg i) := by
    intro n; induction n with
    | zero =>
      rw [queryAllUnsaltedAux_zero]
      exact ⟨fun _ => 0, fixed_oracle_run_pure _ _, fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ n ih =>
      obtain ⟨aVec, hrun, hval⟩ := ih
      rw [queryAllUnsaltedAux_succ, fixed_oracle_run_bind, hrun, pure_bind]
      dsimp only
      by_cases hn : n < LENGTH
      · rw [dif_pos hn, fixed_oracle_run_bind, queryUnsaltedLeaf_fixed, pure_bind, fixed_oracle_run_pure]
        refine ⟨Function.update aVec ⟨n, hn⟩ (leafA c oracle.permutation (msg ⟨n, hn⟩)), rfl, ?_⟩
        intro i hi
        by_cases heq : i = ⟨n, hn⟩
        · subst heq; simp
        · have hlt : i.val < n := by
            have : i.val ≠ n := fun h => heq (Fin.ext h)
            omega
          simp [Function.update_of_ne heq, hval i hlt]
      · rw [dif_neg hn, fixed_oracle_run_pure]
        exact ⟨aVec, rfl, fun i hi => hval i (by have := i.isLt; omega)⟩
  obtain ⟨aVec, hrun, hval⟩ := haux LENGTH
  have ha : aVec = fun i => leafA c oracle.permutation (msg i) := funext fun i => hval i i.isLt
  unfold queryAllUnsalted
  rw [hrun, ha]

private theorem compressionRun_queryCompress_mem (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (permutation : Perm) (x : BitVec 512) (cache : CompressionCache)
    (res : Digest × CompressionCache)
    (hreach : res ∈ support (compressionRun permutation (queryCompress h512 x) cache)) :
    (∀ k v, cache k = some v → res.2 k = some v) ∧
    res.2 (x.cast h512.symm) = some res.1 := by
  have hcr := compression_run_compress permutation (x.cast h512.symm)
    (pure : BitVec COMPRESSION_OUTPUT_LENGTH → OracleComp World Digest) cache
  have hreach' : res ∈ support (compressionRun permutation
      ((liftM (World.query (.inr (.inl (x.cast h512.symm)))) : OracleComp World (BitVec COMPRESSION_OUTPUT_LENGTH)) >>=
        (pure : BitVec COMPRESSION_OUTPUT_LENGTH → OracleComp World Digest)) cache) := hreach
  rw [hcr] at hreach'
  cases hcached : cache (x.cast h512.symm) with
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
    refine ⟨?_, QueryCache.cacheQuery_self cache (x.cast h512.symm) ans⟩
    intro k v hkv
    by_cases hk : k = x.cast h512.symm
    · subst hk; rw [hcached] at hkv; cases hkv
    · erw [QueryCache.cacheQuery_of_ne cache ans hk]; exact hkv

private theorem compressionRun_queryPermute_eq (permutation : Perm) (x : BitVec PERMUTATION_WIDTH)
    (cache : CompressionCache) :
    compressionRun permutation (queryPermute x) cache = pure (permutation x, cache) := by
  have hcr := compression_run_permute permutation x
    (pure : BitVec PERMUTATION_WIDTH → OracleComp World (BitVec PERMUTATION_WIDTH)) cache
  change compressionRun permutation
    ((liftM (World.query (.inr (.inr (.inl x)))) : OracleComp World (BitVec PERMUTATION_WIDTH)) >>=
      (pure : BitVec PERMUTATION_WIDTH → OracleComp World (BitVec PERMUTATION_WIDTH))) cache = _
  rw [hcr, compression_run_pure]

theorem queryAllUnsalted_compressionRun_agrees (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (permutation : Perm) (msg : Message) (cache0 : CompressionCache)
    (res : (Index → Digest) × CompressionCache)
    (hreach : res ∈ support (compressionRun permutation (queryAllUnsalted h512 msg) cache0)) :
    ∀ (table : Compression) (i : Index),
      let c : Comp64 := fun x => tableExtending res.2 table (x.cast h512.symm)
      leafA c permutation (msg i) = res.1 i := by
  have hleaf : ∀ (val : Entry) (cache : CompressionCache) (r : Digest × CompressionCache),
      r ∈ support (compressionRun permutation (queryUnsaltedLeaf h512 val) cache) →
      (∀ k v, cache k = some v → r.2 k = some v) ∧
      (∀ table : Compression,
        let c : Comp64 := fun x => tableExtending r.2 table (x.cast h512.symm)
        leafA c permutation val = r.1) := by
    intro val cache r hr
    unfold queryUnsaltedLeaf at hr
    rw [compression_run_bind] at hr
    obtain ⟨⟨c0, c1⟩, h1, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
    dsimp only at hr
    rw [compression_run_bind] at hr
    erw [compressionRun_queryPermute_eq] at hr
    change r ∈ support (compressionRun permutation
      (queryCompress h512 (leafC2Input (permutation (leafP1Input c0 val)) val)) c1) at hr
    obtain ⟨hp1, hc0⟩ := compressionRun_queryCompress_mem h512 permutation _ cache (c0, c1) h1
    obtain ⟨hp2, ha⟩ := compressionRun_queryCompress_mem h512 permutation _ c1 r hr
    refine ⟨fun k v hkv => hp2 k v (hp1 k v hkv), fun table => ?_⟩
    have hc0_2 : r.2 ((leafC0Input val).cast h512.symm) = some c0 := hp2 _ _ hc0
    have hte : ∀ (x : BitVec 512) (d : Digest), r.2 (x.cast h512.symm) = some d →
        (tableExtending r.2 table (x.cast h512.symm) : Digest) = d := by
      intro x d hx; change (r.2 _).getD _ = _; rw [hx]; rfl
    dsimp only [leafA]
    rw [hte _ _ hc0_2, hte _ _ ha]
  have haux : ∀ n (r : (Index → Digest) × CompressionCache),
      r ∈ support (compressionRun permutation (queryAllUnsaltedAux h512 msg n) cache0) →
      ∀ (table : Compression) (i : Index), i.val < n →
        let c : Comp64 := fun x => tableExtending r.2 table (x.cast h512.symm)
        leafA c permutation (msg i) = r.1 i := by
    intro n; induction n with
    | zero => intro _ _ _ _ hi; exact (Nat.not_lt_zero _ hi).elim
    | succ n ih =>
      intro r hr
      rw [queryAllUnsaltedAux_succ, compression_run_bind] at hr
      obtain ⟨⟨aV, cPrev⟩, hprev, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
      dsimp only at hr
      by_cases hn : n < LENGTH
      · rw [dif_pos hn, compression_run_bind] at hr
        obtain ⟨⟨a, cNext⟩, hleaf_r, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
        dsimp only at hr
        rw [compression_run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst r
        obtain ⟨hpres, hcur⟩ := hleaf (msg ⟨n, hn⟩) cPrev (a, cNext) hleaf_r
        intro table i hi
        by_cases heq : i = ⟨n, hn⟩
        · subst heq; simp only [Function.update_self]; exact hcur table
        · have hlt : i.val < n := by have : i.val ≠ n := fun h => heq (Fin.ext h); omega
          simp only [Function.update_of_ne heq]
          have hfun : (fun x : BitVec 512 => (tableExtending cPrev (tableExtending cNext table) (x.cast h512.symm) : Digest)) =
              (fun x : BitVec 512 => (tableExtending cNext table (x.cast h512.symm) : Digest)) := by
            funext x
            cases hk : cPrev (x.cast h512.symm) with
            | none => change (cPrev _).getD _ = _; rw [hk]; rfl
            | some v =>
              have hv := hpres _ v hk
              change (cPrev _).getD _ = (cNext _).getD _; rw [hk, hv]; rfl
          have hih := ih (aV, cPrev) hprev (tableExtending cNext table) i hlt
          exact (congrArg (fun c : Comp64 => leafA c permutation (msg i)) hfun).symm.trans hih
      · rw [dif_neg hn, compression_run_pure, support_pure, Set.mem_singleton_iff] at hr
        subst r
        intro table i hi
        exact ih (aV, cPrev) hprev table i (by have := i.isLt; omega)
  intro table i
  exact haux LENGTH res hreach table i i.isLt

/-! ### 5. Bottom-Up Oracle Evaluation of the Pure Binary Tree (`queryTreeFromLeafFn`) -/

def queryLevel0Aux (leafFn : Index → OracleComp World Digest) : Nat → OracleComp World (Nat → Digest)
  | 0 => pure (fun _ => 0)
  | n + 1 => do
      let prev ← queryLevel0Aux leafFn n
      if h : n < LENGTH then
        let d ← leafFn ⟨n, h⟩
        pure (Function.update prev n d)
      else pure prev

def queryBinLevelAux (h512 : COMPRESSION_INPUT_LENGTH = 512) (prevLevel : Nat → Digest)
    (lvl : Nat) : Nat → OracleComp World (Nat → Digest)
  | 0 => pure (fun _ => 0)
  | n + 1 => do
      let prev ← queryBinLevelAux h512 prevLevel lvl n
      let raw ← queryCompress h512 (binaryInput (prevLevel (2 * n)) (prevLevel (2 * n + 1)))
      let d := maskLevel lvl raw
      pure (Function.update prev n d)

def queryUpperLevels (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (l0 : Nat → Digest) : Nat → OracleComp World (Nat → Nat → Digest)
  | 0 => pure (fun l idx => if l = 0 then l0 idx else 0)
  | k + 1 => do
      let prev ← queryUpperLevels h512 l0 k
      let cur ← queryBinLevelAux h512 (prev k) (k + 1) (levelSize (k + 1))
      pure (Function.update prev (k + 1) cur)

def queryTreeFromLeafFn (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (leafFn : Index → OracleComp World Digest) : OracleComp World (Nat → Nat → Digest) := do
  let l0 ← queryLevel0Aux leafFn LENGTH
  queryUpperLevels h512 l0 24

private theorem queryLevel0Aux_zero (leafFn : Index → OracleComp World Digest) :
    queryLevel0Aux leafFn 0 = pure (fun _ => 0) := rfl

private theorem queryLevel0Aux_succ (leafFn : Index → OracleComp World Digest) (n : Nat) :
    queryLevel0Aux leafFn (n + 1) = (do
      let prev ← queryLevel0Aux leafFn n
      if h : n < LENGTH then
        let d ← leafFn ⟨n, h⟩
        pure (Function.update prev n d)
      else pure prev) := rfl

private theorem queryBinLevelAux_zero (h512 : COMPRESSION_INPUT_LENGTH = 512) (prevLevel : Nat → Digest)
    (lvl : Nat) :
    queryBinLevelAux h512 prevLevel lvl 0 = pure (fun _ => 0) := rfl

private theorem queryBinLevelAux_succ (h512 : COMPRESSION_INPUT_LENGTH = 512) (prevLevel : Nat → Digest)
    (lvl : Nat) (n : Nat) :
    queryBinLevelAux h512 prevLevel lvl (n + 1) = (do
      let prev ← queryBinLevelAux h512 prevLevel lvl n
      let raw ← queryCompress h512 (binaryInput (prevLevel (2 * n)) (prevLevel (2 * n + 1)))
      let d := maskLevel lvl raw
      pure (Function.update prev n d)) := rfl

private theorem queryUpperLevels_zero (h512 : COMPRESSION_INPUT_LENGTH = 512) (l0 : Nat → Digest) :
    queryUpperLevels h512 l0 0 = pure (fun l idx => if l = 0 then l0 idx else 0) := rfl

private theorem queryUpperLevels_succ (h512 : COMPRESSION_INPUT_LENGTH = 512) (l0 : Nat → Digest) (k : Nat) :
    queryUpperLevels h512 l0 (k + 1) = (do
      let prev ← queryUpperLevels h512 l0 k
      let cur ← queryBinLevelAux h512 (prev k) (k + 1) (levelSize (k + 1))
      pure (Function.update prev (k + 1) cur)) := rfl

private theorem queryTreeFromLeafFn_def (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (leafFn : Index → OracleComp World Digest) :
    queryTreeFromLeafFn h512 leafFn = (do
      let l0 ← queryLevel0Aux leafFn LENGTH
      queryUpperLevels h512 l0 24) := rfl

attribute [irreducible] queryLevel0Aux queryBinLevelAux queryUpperLevels queryTreeFromLeafFn

private theorem sum_bin_calls_eq :
    (∑ k ∈ Finset.range 24, levelSize (k + 1)) = LENGTH - 1 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [levelSize, LENGTH, LOG_LENGTH]

theorem queryTreeFromLeafFn_bound_one (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (leafFn : Index → OracleComp World Digest)
    (hleaf : ∀ i, PublicQueryBound (leafFn i) 1) :
    PublicQueryBound (queryTreeFromLeafFn h512 leafFn) IDEAL_TREE_BUDGET := by
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
  have hbin : ∀ pl lvl n, PublicQueryBound (queryBinLevelAux h512 pl lvl n) n := by
    intro pl lvl n; induction n with
    | zero => rw [queryBinLevelAux_zero]; exact public_query_bound_pure' _ _
    | succ n ih =>
      rw [queryBinLevelAux_succ]
      apply public_query_bound_bind ih
      intro _
      simpa only [Nat.add_zero] using public_query_bound_bind (queryCompress_bound h512 _) (fun _ => public_query_bound_pure' _ 0)
  have hup : ∀ l0 k, PublicQueryBound (queryUpperLevels h512 l0 k) (∑ j ∈ Finset.range k, levelSize (j + 1)) := by
    intro l0 k; induction k with
    | zero =>
      rw [queryUpperLevels_zero]
      simp only [Finset.range_zero, Finset.sum_empty]
      exact public_query_bound_pure' _ _
    | succ k ih =>
      rw [queryUpperLevels_succ, Finset.sum_range_succ]
      apply public_query_bound_bind ih
      intro prev
      simpa only [Nat.add_zero] using public_query_bound_bind (hbin _ _ _) (fun _ => public_query_bound_pure' _ 0)
  rw [queryTreeFromLeafFn_def]
  unfold IDEAL_TREE_BUDGET
  refine public_query_bound_bind (hl0 LENGTH) fun l0 => ?_
  rw [← sum_bin_calls_eq]
  exact hup l0 24

theorem queryTreeFromLeafFn_fixed (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (leafFn : Index → OracleComp World Digest) (leaves : Index → Digest)
    (hleaf : ∀ i, fixedOracleRun oracle (leafFn i) = pure (leaves i)) :
    ∃ nodes,
      fixedOracleRun oracle (queryTreeFromLeafFn h512 leafFn) = pure nodes ∧
      ∀ l ≤ 24, ∀ idx < levelSize l,
        nodes l idx = nodeValFromLeaves (fun x => oracle.compression (x.cast h512.symm)) leaves l idx := by
  let c : Comp64 := oracleComp64 h512 oracle
  have hl0 : ∀ n, ∃ f, fixedOracleRun oracle (queryLevel0Aux leafFn n) = pure f ∧
      ∀ idx < n, idx < LENGTH → f idx = nodeValFromLeaves c leaves 0 idx := by
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
        · subst heq; simp [nodeValFromLeaves, hn]
        · rw [Function.update_of_ne heq]; exact hval idx (by omega) hlen
      · rw [dif_neg hn, fixed_oracle_run_pure]
        exact ⟨f, rfl, fun idx hlt hlen => hval idx (by omega) hlen⟩
  obtain ⟨l0, hl0_run, hl0_val⟩ := hl0 LENGTH
  have hl0_all : ∀ idx < levelSize 0, l0 idx = nodeValFromLeaves c leaves 0 idx :=
    fun idx h => hl0_val idx (by rwa [levelSize_0, show (16777216 : Nat) = LENGTH by decide] at h)
      (by rwa [levelSize_0, show (16777216 : Nat) = LENGTH by decide] at h)
  have hbin : ∀ (prevLvl : Nat) (hlt24 : prevLvl < 24)
      (prevArr : Nat → Digest) (hprev : ∀ idx < levelSize prevLvl, prevArr idx = nodeValFromLeaves c leaves prevLvl idx)
      (n : Nat) (hn : n ≤ levelSize (prevLvl + 1)),
      ∃ f, fixedOracleRun oracle (queryBinLevelAux h512 prevArr (prevLvl + 1) n) = pure f ∧
        ∀ idx < n, f idx = nodeValFromLeaves c leaves (prevLvl + 1) idx := by
    intro prevLvl hlt24 prevArr hprev n hn
    have hd := levelSize_double prevLvl hlt24
    induction n with
    | zero =>
      rw [queryBinLevelAux_zero]
      exact ⟨_, fixed_oracle_run_pure _ _, fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ n ih =>
      obtain ⟨f, hrun, hval⟩ := ih (by omega)
      rw [queryBinLevelAux_succ, fixed_oracle_run_bind, hrun, pure_bind, fixed_oracle_run_bind,
        queryCompress_fixed, pure_bind, fixed_oracle_run_pure]
      refine ⟨Function.update f n _, rfl, ?_⟩
      intro idx hlt
      by_cases heq : idx = n
      · subst heq
        simp only [Function.update_self, nodeValFromLeaves, show idx < levelSize (prevLvl + 1) by omega, ite_true]
        rw [hprev (2 * idx) (by omega), hprev (2 * idx + 1) (by omega)]
      · rw [Function.update_of_ne heq]; exact hval idx (by omega)
  have hup : ∀ k ≤ 24, ∃ arr, fixedOracleRun oracle (queryUpperLevels h512 l0 k) = pure arr ∧
      ∀ l ≤ k, ∀ idx < levelSize l, arr l idx = nodeValFromLeaves c leaves l idx := by
    intro k hk; induction k with
    | zero =>
      rw [queryUpperLevels_zero]
      refine ⟨_, fixed_oracle_run_pure _ _, ?_⟩
      intro l hl idx hidx
      have h0 : l = 0 := by omega
      subst h0; simp only [ite_true]; exact hl0_all idx hidx
    | succ k ih =>
      obtain ⟨arr, hrun, hval⟩ := ih (by omega)
      rw [queryUpperLevels_succ, fixed_oracle_run_bind, hrun, pure_bind]
      obtain ⟨cur, hcur_run, hcur_val⟩ := hbin k (by omega) (arr k) (hval k (le_refl _))
        (levelSize (k + 1)) (le_refl _)
      rw [fixed_oracle_run_bind, hcur_run, pure_bind, fixed_oracle_run_pure]
      refine ⟨Function.update arr (k + 1) cur, rfl, ?_⟩
      intro l hl idx hidx
      by_cases hltop : l = k + 1
      · subst hltop; rw [Function.update_self]; exact hcur_val idx hidx
      · rw [Function.update_of_ne hltop]; exact hval l (by omega) idx hidx
  obtain ⟨nodes, hup_run, hup_val⟩ := hup 24 (le_refl _)
  rw [queryTreeFromLeafFn_def, fixed_oracle_run_bind, hl0_run, pure_bind, hup_run]
  exact ⟨nodes, rfl, hup_val⟩

/-! ### 6. Pure `GoodIdealTrace` Invariant for `queryTreeFromLeafFn (idealLeafFn ...)` -/

def GoodIdealQuery (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (aVec : Index → Digest) (sOpen : Index → Salt192) (leafRand : Index → Digest)
    (positions : Positions) (trace : CompressionReplies) (x : BitVec COMPRESSION_INPUT_LENGTH) : Prop :=
  (∃ i ∈ positions, x = (leafFinalInput i (aVec i) (sOpen i)).cast h512.symm) ∨
  (((∃ j ∉ positions, x.extractLsb' 0 238 = low238 (leafRand j)) ∨
    (∃ pair ∈ trace, x.extractLsb' 0 238 = low238 pair.2)) ∧
   ((∃ j ∉ positions, x.extractLsb' 256 238 = low238 (leafRand j)) ∨
    (∃ pair ∈ trace, x.extractLsb' 256 238 = low238 pair.2)))

def GoodIdealTrace (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (aVec : Index → Digest) (sOpen : Index → Salt192) (leafRand : Index → Digest)
    (positions : Positions) (trace : CompressionReplies) : Prop :=
  ∀ pair ∈ trace, GoodIdealQuery h512 aVec sOpen leafRand positions trace pair.1

private theorem good_ideal_query_mono {h512 : COMPRESSION_INPUT_LENGTH = 512}
    {aVec : Index → Digest} {sOpen : Index → Salt192} {leafRand : Index → Digest}
    {positions : Positions} {t1 t2 : CompressionReplies} (hsub : ∀ p ∈ t1, p ∈ t2) {x}
    (hg : GoodIdealQuery h512 aVec sOpen leafRand positions t1 x) :
    GoodIdealQuery h512 aVec sOpen leafRand positions t2 x := by
  rcases hg with hopen | ⟨hlo, hhi⟩
  · exact Or.inl hopen
  · refine Or.inr ⟨?_, ?_⟩
    · rcases hlo with h | ⟨p, hp, heq⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, hsub p hp, heq⟩
    · rcases hhi with h | ⟨p, hp, heq⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, hsub p hp, heq⟩

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

private theorem traceReplies_queryCompress_fixed (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (x : BitVec 512) :
    fixedOracleRun oracle (traceCompressionReplies (queryCompress h512 x)) =
      (pure (oracle.compression (x.cast h512.symm),
        [(x.cast h512.symm, (oracle.compression (x.cast h512.symm) : Digest))]) :
        ProbComp (Digest × CompressionReplies)) := by
  unfold queryCompress
  change fixedOracleRun oracle ((liftM (World.query (.inr (.inl (x.cast h512.symm)))) : OracleComp World Digest) >>=
    fun (ans : Digest) => (pure (ans, ([] : CompressionReplies)) : OracleComp World (Digest × CompressionReplies)) >>=
      fun (v, tr) => pure (v, (x.cast h512.symm, ans) :: tr)) = _
  rw [fixed_oracle_run_compress, pure_bind]
  exact fixed_oracle_run_pure oracle (α := Digest × CompressionReplies) _

def idealLeafFn (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (aVec : Index → Digest) (sOpen : Index → Salt192) (leafRand : Index → Digest)
    (positions : Positions) (i : Index) : OracleComp World Digest :=
  if i ∈ positions then
    queryCompress h512 (leafFinalInput i (aVec i) (sOpen i))
  else
    pure (leafRand i)

theorem idealLeafFn_bound (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (aVec : Index → Digest) (sOpen : Index → Salt192) (leafRand : Index → Digest)
    (positions : Positions) (i : Index) :
    PublicQueryBound (idealLeafFn h512 aVec sOpen leafRand positions i) 1 := by
  unfold idealLeafFn
  by_cases hi : i ∈ positions
  · rw [if_pos hi]; exact queryCompress_bound h512 _
  · rw [if_neg hi]; exact public_query_bound_pure' _ _

theorem queryIdealTree_good_trace (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (aVec : Index → Digest) (sOpen : Index → Salt192)
    (leafRand : Index → Digest) (positions : Positions) :
    ∃ nodes trace,
      fixedOracleRun oracle (traceCompressionReplies
        (queryTreeFromLeafFn h512 (idealLeafFn h512 aVec sOpen leafRand positions))) = pure (nodes, trace) ∧
      GoodIdealTrace h512 aVec sOpen leafRand positions trace := by
  have hcast0 : ∀ (x : BitVec 512), (x.cast h512.symm).extractLsb' 0 238 = x.extractLsb' 0 238 :=
    fun x => extractLsb'_cast_eq h512.symm x 0 238
  have hcast256 : ∀ (x : BitVec 512), (x.cast h512.symm).extractLsb' 256 238 = x.extractLsb' 256 238 :=
    fun x => extractLsb'_cast_eq h512.symm x 256 238
  have hleaf : ∀ i : Index, ∃ d tr,
      fixedOracleRun oracle (traceCompressionReplies (idealLeafFn h512 aVec sOpen leafRand positions i)) = pure (d, tr) ∧
      GoodIdealTrace h512 aVec sOpen leafRand positions tr ∧
      ((∃ k ∉ positions, low238 d = low238 (leafRand k)) ∨ (∃ p ∈ tr, low238 d = low238 p.2)) := by
    intro i
    unfold idealLeafFn
    by_cases hi : i ∈ positions
    · rw [if_pos hi]
      let x := (leafFinalInput i (aVec i) (sOpen i)).cast h512.symm
      let d : Digest := oracle.compression x
      refine ⟨d, [(x, d)], traceReplies_queryCompress_fixed h512 oracle _, ?_, Or.inr ⟨(x, d), by simp, rfl⟩⟩
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact Or.inl ⟨i, hi, rfl⟩
    · rw [if_neg hi]
      exact ⟨leafRand i, [], by simp only [traceReplies_pure, fixed_oracle_run_pure],
        by simp [GoodIdealTrace], Or.inl ⟨i, hi, rfl⟩⟩
  have hl0 : ∀ n, ∃ f tr,
      fixedOracleRun oracle (traceCompressionReplies (queryLevel0Aux (idealLeafFn h512 aVec sOpen leafRand positions) n)) = pure (f, tr) ∧
      GoodIdealTrace h512 aVec sOpen leafRand positions tr ∧
      ∀ idx < n, idx < LENGTH → ((∃ k ∉ positions, low238 (f idx) = low238 (leafRand k)) ∨ (∃ p ∈ tr, low238 (f idx) = low238 p.2)) := by
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
  have hbin : ∀ (prevTr : CompressionReplies) (hpg : GoodIdealTrace h512 aVec sOpen leafRand positions prevTr)
      (prevArr : Nat → Digest) (ps : Nat) (lvl : Nat)
      (hprev : ∀ idx < ps, (∃ k ∉ positions, low238 (prevArr idx) = low238 (leafRand k)) ∨
        (∃ p ∈ prevTr, low238 (prevArr idx) = low238 p.2))
      (n : Nat) (hn : 2 * n ≤ ps),
      ∃ f tr,
        fixedOracleRun oracle (traceCompressionReplies (queryBinLevelAux h512 prevArr lvl n)) = pure (f, tr) ∧
        GoodIdealTrace h512 aVec sOpen leafRand positions (prevTr ++ tr) ∧
        ∀ idx < n, (∃ k ∉ positions, low238 (f idx) = low238 (leafRand k)) ∨
          (∃ p ∈ prevTr ++ tr, low238 (f idx) = low238 p.2) := by
    intro prevTr hpg prevArr ps lvl hprev n hn
    induction n with
    | zero =>
      refine ⟨fun _ => 0, [],
        by simp only [queryBinLevelAux_zero, traceReplies_pure, fixed_oracle_run_pure], by simpa using hpg,
        fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ n ih =>
      obtain ⟨f, tr, hrun, hgood, hval⟩ := ih (by omega)
      rw [queryBinLevelAux_succ]
      let x := (binaryInput (prevArr (2 * n)) (prevArr (2 * n + 1))).cast h512.symm
      let raw : Digest := oracle.compression x
      let d : Digest := maskLevel lvl raw
      have hrunb :
          fixedOracleRun oracle (traceCompressionReplies (do
            let prev ← queryBinLevelAux h512 prevArr lvl n
            let raw' ← queryCompress h512 (binaryInput (prevArr (2 * n)) (prevArr (2 * n + 1)))
            let d' := maskLevel lvl raw'
            pure (Function.update prev n d'))) =
          pure (Function.update f n d, tr ++ [(x, raw)]) := by
        simp only [traceReplies_bind, traceReplies_pure, fixed_oracle_run_bind, fixed_oracle_run_pure,
          traceReplies_queryCompress_fixed, hrun, pure_bind, List.append_nil]
        rfl
      refine ⟨Function.update f n d, tr ++ [(x, raw)], hrunb, ?_, ?_⟩
      · intro p hp
        have hmem_sub : ∀ q ∈ prevTr ++ tr, q ∈ prevTr ++ (tr ++ [(x, raw)]) := by
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
          · rcases hprev (2 * n) (by omega) with ⟨k, hk, hkeq⟩ | ⟨q, hq, hqeq⟩
            · left; refine ⟨k, hk, ?_⟩
              dsimp only [x]; rw [hcast0, binaryInput_lo238, hkeq]
            · right; refine ⟨q, List.mem_append_left _ hq, ?_⟩
              dsimp only [x]; rw [hcast0, binaryInput_lo238, hqeq]
          · rcases hprev (2 * n + 1) (by omega) with ⟨k, hk, hkeq⟩ | ⟨q, hq, hqeq⟩
            · left; refine ⟨k, hk, ?_⟩
              dsimp only [x]; rw [hcast256, binaryInput_hi238, hkeq]
            · right; refine ⟨q, List.mem_append_left _ hq, ?_⟩
              dsimp only [x]; rw [hcast256, binaryInput_hi238, hqeq]
      · intro idx hlt
        by_cases heq : idx = n
        · subst heq; rw [Function.update_self]
          right; refine ⟨(x, raw), by simp, ?_⟩
          exact low238_maskLevel lvl raw
        · rw [Function.update_of_ne heq]
          rcases hval idx (by omega) with hlr | ⟨p, hp, hpeq⟩
          · exact Or.inl hlr
          · refine Or.inr ⟨p, ?_, hpeq⟩
            rcases List.mem_append.mp hp with h1 | h2
            · exact List.mem_append_left _ h1
            · exact List.mem_append_right _ (List.mem_append_left _ h2)
  have hup : ∀ k ≤ 24, ∃ arr tr,
      fixedOracleRun oracle (traceCompressionReplies (queryUpperLevels h512 l0 k)) = pure (arr, tr) ∧
      GoodIdealTrace h512 aVec sOpen leafRand positions (tr0 ++ tr) ∧
      ∀ l ≤ k, ∀ idx < levelSize l,
        (∃ j ∉ positions, low238 (arr l idx) = low238 (leafRand j)) ∨
        (∃ p ∈ tr0 ++ tr, low238 (arr l idx) = low238 p.2) := by
    intro k hk; induction k with
    | zero =>
      refine ⟨fun l idx => if l = 0 then l0 idx else 0, [],
        by simp only [queryUpperLevels_zero, traceReplies_pure, fixed_oracle_run_pure], by simpa using htr0_good, ?_⟩
      intro l hl idx hidx
      have h0 : l = 0 := by omega
      subst h0
      simp only [List.append_nil, ite_true]
      have hidx' : idx < LENGTH := by rwa [levelSize_0, show (16777216 : Nat) = LENGTH by decide] at hidx
      exact htr0_nodes idx hidx' hidx'
    | succ k ih =>
      obtain ⟨arr, tr, hrun, hgood, hval⟩ := ih (by omega)
      rw [queryUpperLevels_succ, traceReplies_bind, fixed_oracle_run_bind, hrun, pure_bind]
      dsimp only
      have hd := levelSize_double k (by omega)
      obtain ⟨cur, trc, hcrun, hcgood, hclt⟩ := hbin (tr0 ++ tr) hgood
        (arr k) (levelSize k) (k + 1) (hval k (le_refl _))
        (levelSize (k + 1)) (by omega)
      simp only [traceReplies_bind, traceReplies_pure, fixed_oracle_run_bind, fixed_oracle_run_pure,
        hcrun, pure_bind, List.append_nil]
      refine ⟨Function.update arr (k + 1) cur, tr ++ trc, rfl, ?_, ?_⟩
      · simpa [List.append_assoc] using hcgood
      · intro l hl idx hidx
        by_cases htop : l = k + 1
        · subst htop; rw [Function.update_self]
          simpa [List.append_assoc] using hclt idx hidx
        · rw [Function.update_of_ne htop]
          rcases hval l (by omega) idx hidx with hlr | ⟨p, hp, hpeq⟩
          · exact Or.inl hlr
          · refine Or.inr ⟨p, ?_, hpeq⟩
            rcases List.mem_append.mp hp with h1 | h2
            · exact List.mem_append_left _ h1
            · exact List.mem_append_right _ (List.mem_append_left _ h2)
  obtain ⟨nodes, trUp, hup_run, hup_good, _⟩ := hup 24 (le_refl _)
  rw [queryTreeFromLeafFn_def]
  simp only [traceReplies_bind, fixed_oracle_run_bind, fixed_oracle_run_pure,
    htr0_run, hup_run, pure_bind]
  exact ⟨nodes, tr0 ++ trUp, rfl, hup_good⟩

end CommitGolfCandidate
