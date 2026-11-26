import CommitGolfCandidate.HidingCache

/-! Hiding of a leaf tail chain starting from a uniform 256-bit initial digest
(`leafDigestFromInit`) against a bounded oracle continuation. -/
namespace CommitGolfCandidate

local instance hidingLeafDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleComp.DeferredSampling

set_option maxHeartbeats 200000

/-- Oracle program for the compression chain, used only in the security proof. -/
def hashBlocks : List LeafBlock → Digest → OracleComp World Digest
  | [], state => pure state
  | block :: rest, state => do
      let answer ← (liftM (World.query (.inr (.inl ((leafInput state block))))) : OracleComp World Digest)
      hashBlocks rest answer

theorem hash_blocks_bound (blocks : List LeafBlock) (state : Digest) :
    PublicQueryBound (hashBlocks blocks state) blocks.length := by
  induction blocks generalizing state with
  | nil => trivial
  | cons block rest ih =>
    change 1 ≤ rest.length+1 ∧ ∀ answer,
      PublicQueryBound (hashBlocks rest answer) (rest.length+1-1)
    exact ⟨by omega, fun answer => by simpa only [Nat.add_sub_cancel] using ih answer⟩

theorem fixed_hash_blocks (oracle : Oracle) (blocks : List LeafBlock) (state : Digest)
    {α : Type} (next : Digest → OracleComp World α) :
    fixedOracleRun oracle (hashBlocks blocks state >>= next) =
      fixedOracleRun oracle (next (blocks.foldl
        (fun state block => absorb oracle.compression state block) state)) := by
  induction blocks generalizing state with
  | nil => rfl
  | cons block rest ih =>
    simp only [hashBlocks, bind_assoc, List.foldl_cons]
    erw [fixed_oracle_run_public]
    exact ih (oracle.compression ((leafInput state block)))

/-- Replacing each intermediate chaining value in turn gives a linear hybrid bound. -/
theorem salted_chain_distance (permutation : Perm) (blocks : List LeafBlock)
    {α : Type} (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ Digest
          fixedOracleRun ⟨table, permutation⟩
            (next (blocks.foldl (fun state block => absorb table state block) salt)))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Digest
          fixedOracleRun ⟨table, permutation⟩ (next answer)) ≤
      (blocks.length : ℝ) * ((budget + blocks.length : Nat) : ℝ) / 2^256 := by
  induction blocks with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.cast_zero, zero_mul, zero_div,
      measureTVDist_self, le_refl]
  | cons block rest ih =>
    let continuation : Digest → OracleComp World α := fun state => hashBlocks rest state >>= next
    have continued : ∀ state, PublicQueryBound (continuation state) (rest.length + budget) :=
      fun state => public_query_bound_bind (hash_blocks_bound rest state) bounded
    have first := salted_compression_distance permutation block continuation (rest.length + budget) continued
    simp only [continuation, fixed_hash_blocks] at first
    have triangle := measureTVDist_triangle (m := ProbComp)
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ Digest
          fixedOracleRun ⟨table, permutation⟩
            (next ((block :: rest).foldl (fun state block => absorb table state block) salt)))
      (do let table ← $ᵗ Compression
          let state ← $ᵗ Digest
          fixedOracleRun ⟨table, permutation⟩
            (next (rest.foldl (fun state block => absorb table state block) state)))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Digest
          fixedOracleRun ⟨table, permutation⟩ (next answer))
    simp only [List.foldl_cons] at triangle ⊢
    have combined := triangle.trans (add_le_add first ih)
    refine combined.trans ?_
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have nonnegative : (0 : ℝ) ≤ rest.length := Nat.cast_nonneg _
    nlinarith

/-- For the 3-block tail leaf chain `leafDigestFromInit`, a fresh 256-bit initial digest
allows replacement of the leaf digest by a fresh uniform digest at cost `8*(budget+8)/2^256`. -/
theorem salted_leaf_distance (permutation : Perm) (value : Entry)
    {α : Type} (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let init ← $ᵗ Digest
          fixedOracleRun ⟨table, permutation⟩ (next (leafDigestFromInit table init value)))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Digest
          fixedOracleRun ⟨table, permutation⟩ (next answer)) ≤
      8 * ((budget + 8 : Nat) : ℝ) / 2^256 := by
  have result := salted_chain_distance permutation (leafTailBlocks value) next budget bounded
  simp only [leafTailBlocks, List.length_map, List.length_range, leafDigestFromInit, Nat.cast_ofNat] at result
  refine result.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  have nonnegative : (0 : ℝ) ≤ budget := Nat.cast_nonneg _
  push_cast
  nlinarith

/-- The chain bound also includes all compression inputs known before the initial digest
was drawn. -/
theorem cached_salted_chain_distance (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (blocks : List LeafBlock)
    {α : Type} (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩
            (next (blocks.foldl (fun state block => absorb (tableExtending cache table) state block) salt)))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next answer)) ≤
      (blocks.length : ℝ) * ((keys.card + budget + blocks.length : Nat) : ℝ) / 2^256 := by
  induction blocks with
  | nil => simp only [List.foldl_nil, List.length_nil, Nat.cast_zero, zero_mul, zero_div,
      measureTVDist_self, le_refl]
  | cons block rest ih =>
    let continuation : Digest → OracleComp World α := fun state => hashBlocks rest state >>= next
    have continued : ∀ state, PublicQueryBound (continuation state) (rest.length + budget) :=
      fun state => public_query_bound_bind (hash_blocks_bound rest state) bounded
    have first := cached_salted_compression_distance permutation cache keys covered block continuation (rest.length + budget) continued
    simp only [continuation, fixed_hash_blocks] at first
    have triangle := measureTVDist_triangle (m := ProbComp)
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩
            (next ((block :: rest).foldl (fun state block => absorb (tableExtending cache table) state block) salt)))
      (do let table ← $ᵗ Compression
          let state ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩
            (next (rest.foldl (fun state block => absorb (tableExtending cache table) state block) state)))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next answer))
    simp only [List.foldl_cons] at triangle ⊢
    have combined := triangle.trans (add_le_add first ih)
    refine combined.trans ?_
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have nonnegative : (0 : ℝ) ≤ rest.length := Nat.cast_nonneg _
    nlinarith

/-- A private 3-block tail leaf remains hidden with a fixed prior query transcript. -/
theorem cached_salted_leaf_distance (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (value : Entry)
    {α : Type} (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let init ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩
            (next (leafDigestFromInit (tableExtending cache table) init value)))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next answer)) ≤
      8 * ((keys.card + budget + 8 : Nat) : ℝ) / 2^256 := by
  have result := cached_salted_chain_distance permutation cache keys covered
    (leafTailBlocks value) next budget bounded
  simp only [leafTailBlocks, List.length_map, List.length_range, leafDigestFromInit, Nat.cast_ofNat] at result
  refine result.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  have nonnegative : (0 : ℝ) ≤ budget := Nat.cast_nonneg _
  have nonnegativeKeys : (0 : ℝ) ≤ keys.card := Nat.cast_nonneg _
  push_cast
  nlinarith

/-- Any two leaf values are indistinguishable in `leafDigestFromInit` when given a fresh
uniform 256-bit initial digest. -/
theorem cached_leaf_indistinguishable (permutation : Perm) (cache : CompressionCache)
    (keys : Finset (BitVec COMPRESSION_INPUT_LENGTH)) (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (left right : Entry) {α : Type} (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let init ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩
            (next (leafDigestFromInit (tableExtending cache table) init left)))
      (do let table ← $ᵗ Compression
          let init ← $ᵗ Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩
            (next (leafDigestFromInit (tableExtending cache table) init right))) ≤
      16 * ((keys.card + budget + 8 : Nat) : ℝ) / 2^256 := by
  have leftBound := cached_salted_leaf_distance permutation cache keys covered left next budget bounded
  have rightBound := cached_salted_leaf_distance permutation cache keys covered right next budget bounded
  rw [measureTVDist_comm] at rightBound
  have triangle := measureTVDist_triangle (m := ProbComp)
    (do let table ← $ᵗ Compression
        let init ← $ᵗ Digest
        fixedOracleRun ⟨tableExtending cache table, permutation⟩
          (next (leafDigestFromInit (tableExtending cache table) init left)))
    (do let table ← $ᵗ Compression
        let answer ← $ᵗ Digest
        fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next answer))
    (do let table ← $ᵗ Compression
        let init ← $ᵗ Digest
        fixedOracleRun ⟨tableExtending cache table, permutation⟩
          (next (leafDigestFromInit (tableExtending cache table) init right)))
  refine (triangle.trans (add_le_add leftBound rightBound)).trans ?_
  exact le_of_eq (by ring)

end CommitGolfCandidate
