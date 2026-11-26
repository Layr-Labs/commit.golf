import CommitGolfCandidate.CompressionSampling

/-! Core definitions for public-query row recording and the cross-oracle permutation
witness (`C3PermWitness`) used by our `C0 -> P1 -> C2 -> C3` leaf binding proof. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

set_option autoImplicit false
set_option maxRecDepth 8192

abbrev Block := BitVec PERMUTATION_WIDTH

/-- First 32 bytes (256 bits) of a 200-byte permutation output. -/
def outputDigest (output : Block) : BitVec 256 := output.extractLsb' 0 256

/-- Last 32 bytes (bits `1344..1600`) of a 200-byte permutation input (`c0 = C(v[192..256))`). -/
def c3T3Field (input : Block) : BitVec 256 := input.extractLsb' 1344 256

/-- One public oracle query and its reply. Both forward and inverse permutation queries
record `(input, output)` with `P(input) = output`. -/
inductive PublicRow where
  | compression (input : BitVec COMPRESSION_INPUT_LENGTH) (reply : BitVec 256)
  | permutation (input reply : Block)

def queryRows (query : World.Domain) (answer : World.Range query) : List PublicRow :=
  match query with
  | .inl _ => []
  | .inr (.inl input) => [.compression input answer]
  | .inr (.inr (.inl input)) => [.permutation input answer]
  | .inr (.inr (.inr output)) => [.permutation answer output]

def recordRows {α : Type} (program : OracleComp World α) : OracleComp World (α × List PublicRow) :=
  OracleComp.recOn program (fun value => pure (value, []))
    (fun query _ next => do
      let answer ← (liftM (World.query query) : OracleComp World _)
      (fun result => (result.1, queryRows query answer ++ result.2)) <$> next answer)

theorem record_rows_pure {α : Type} (value : α) :
    recordRows (pure value : OracleComp World α) = pure (value, []) := rfl

theorem record_rows_query {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) :
    recordRows ((liftM (World.query query) : OracleComp World _) >>= next) =
      (do let answer ← (liftM (World.query query) : OracleComp World _)
          (fun result => (result.1, queryRows query answer ++ result.2)) <$> recordRows (next answer)) := rfl

theorem record_rows_bound {α : Type} (program : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound program budget) : PublicQueryBound (recordRows program) budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure _ => trivial
  | query_bind query next ih =>
    rw [record_rows_query]
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    refine ⟨bounded.1, fun answer => ?_⟩
    exact (isQueryBound_map_iff _ _ _ _ _).mpr (ih answer _ (bounded.2 answer))

theorem record_rows_bind {α β : Type} (program : OracleComp World α) (next : α → OracleComp World β) :
    recordRows (program >>= next) = (do
      let earlier ← recordRows program
      let later ← recordRows (next earlier.1)
      pure (later.1, earlier.2 ++ later.2)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [record_rows_pure]
  | query_bind query tail ih =>
    rw [bind_assoc, record_rows_query, record_rows_query]
    simp only [bind_assoc]
    apply bind_congr
    intro answer
    rw [ih]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, List.append_assoc]

theorem record_rows_erase {α : Type} (program : OracleComp World α) :
    Prod.fst <$> recordRows program = program := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [record_rows_pure]
  | query_bind query next ih =>
    rw [record_rows_query, map_bind]
    apply bind_congr
    intro answer
    simpa only [Functor.map_map, Function.comp_def] using ih answer

/-- Every recorded compression row in `recordRows program` is present in the terminal lazy cache. -/
theorem record_rows_compressionRun_cache (permutation : Perm) {α : Type}
    (program : OracleComp World α) (cache : CompressionCache)
    (result : (α × List PublicRow) × CompressionCache)
    (reached : result ∈ support (compressionRun permutation (recordRows program) cache)) :
    (∀ k v, cache k = some v → result.2 k = some v) ∧
    (∀ x a, PublicRow.compression x a ∈ result.1.2 → result.2 x = some a) := by
  induction program using OracleComp.inductionOn generalizing cache result with
  | pure value =>
    rw [record_rows_pure, compression_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact ⟨fun _ _ h => h, by simp⟩
  | query_bind query next ih =>
    rw [record_rows_query] at reached
    rcases query with coins | publicQuery
    · rw [compression_run_private] at reached
      obtain ⟨answer, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
      rw [compression_run_map, support_map] at reached
      obtain ⟨⟨⟨v, rows⟩, c'⟩, hreach, rfl⟩ := reached
      obtain ⟨hpres, hmem⟩ := ih answer cache ((v, rows), c') hreach
      exact ⟨hpres, fun x a hx => hmem x a (by simpa [queryRows] using hx)⟩
    · rcases publicQuery with input | permQuery
      · rw [compression_run_compress] at reached
        cases hcached : cache input with
        | some answer =>
          rw [hcached] at reached
          dsimp only at reached
          rw [compression_run_map, support_map] at reached
          obtain ⟨⟨⟨v, rows⟩, c'⟩, hreach, rfl⟩ := reached
          obtain ⟨hpres, hmem⟩ := ih answer cache ((v, rows), c') hreach
          refine ⟨hpres, fun x a hx => ?_⟩
          simp only [queryRows, List.singleton_append, List.mem_cons] at hx
          rcases hx with heq | htail
          · cases heq
            exact hpres input answer hcached
          · exact hmem x a htail
        | none =>
          rw [hcached] at reached
          dsimp only at reached
          obtain ⟨answer, _, reached⟩ := (mem_support_bind_iff _ _ _).mp reached
          rw [compression_run_map, support_map] at reached
          obtain ⟨⟨⟨v, rows⟩, c'⟩, hreach, rfl⟩ := reached
          obtain ⟨hpres, hmem⟩ := ih answer (cache.cacheQuery input answer) ((v, rows), c') hreach
          refine ⟨?_, ?_⟩
          · intro k v' hkv
            apply hpres
            by_cases hk : k = input
            · subst hk; rw [hcached] at hkv; cases hkv
            · erw [QueryCache.cacheQuery_of_ne cache answer hk]; exact hkv
          · intro x a hx
            simp only [queryRows, List.singleton_append, List.mem_cons] at hx
            rcases hx with heq | htail
            · cases heq
              exact hpres input answer (QueryCache.cacheQuery_self cache input answer)
            · exact hmem x a htail
      · rcases permQuery with input | output
        · rw [compression_run_permute, compression_run_map, support_map] at reached
          obtain ⟨⟨⟨v, rows⟩, c'⟩, hreach, rfl⟩ := reached
          obtain ⟨hpres, hmem⟩ := ih _ cache ((v, rows), c') hreach
          refine ⟨hpres, fun x a hx => ?_⟩
          simp only [queryRows, List.singleton_append, List.mem_cons] at hx
          rcases hx with heq | htail
          · cases heq
          · exact hmem x a htail
        · rw [compression_run_inverse, compression_run_map, support_map] at reached
          obtain ⟨⟨⟨v, rows⟩, c'⟩, hreach, rfl⟩ := reached
          obtain ⟨hpres, hmem⟩ := ih _ cache ((v, rows), c') hreach
          refine ⟨hpres, fun x a hx => ?_⟩
          simp only [queryRows, List.singleton_append, List.mem_cons] at hx
          rcases hx with heq | htail
          · cases heq
          · exact hmem x a htail

/-- Two recorded permutation rows with different inputs and equal 256-bit output prefixes,
where the `c3T3Field` (bits `1344..1600`) of each input is the reply of a recorded compression row. -/
def C3PermWitness (rows : List PublicRow) : Prop :=
  ∃ (input₀ input₁ reply₀ reply₁ : Block) (source₀ source₁ : BitVec COMPRESSION_INPUT_LENGTH),
    PublicRow.permutation input₀ reply₀ ∈ rows ∧ PublicRow.permutation input₁ reply₁ ∈ rows ∧
    PublicRow.compression source₀ (c3T3Field input₀) ∈ rows ∧
    PublicRow.compression source₁ (c3T3Field input₁) ∈ rows ∧
    input₀ ≠ input₁ ∧ outputDigest reply₀ = outputDigest reply₁

theorem C3PermWitness.mono {earlier later : List PublicRow}
    (contained : ∀ row ∈ earlier, row ∈ later)
    (witness : C3PermWitness earlier) : C3PermWitness later := by
  obtain ⟨x₀, x₁, y₀, y₁, a₀, a₁, h₀, h₁, c₀, c₁, different, equal⟩ := witness
  exact ⟨x₀, x₁, y₀, y₁, a₀, a₁, contained _ h₀, contained _ h₁, contained _ c₀, contained _ c₁,
    different, equal⟩

end CommitGolfCandidate
