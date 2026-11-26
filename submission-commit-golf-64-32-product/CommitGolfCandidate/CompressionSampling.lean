import CommitGolfCandidate.Probability
import CommitGolfCandidate.CompressionROM
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-! Relate lazy compression sampling to the contract's uniformly sampled full
function. The permutation is fixed throughout, and private coins are forwarded
unchanged. Equality is distributional; no full truth table is constructed by a
submitted machine. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance compressionSamplingDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

/-- Discard only the runner's accounting output, retaining its exact distribution. -/
def fixedOracleRun (oracle : Oracle) {α : Type} (computation : OracleComp World α) : ProbComp α :=
  Prod.fst <$> oracle.run computation

theorem fixed_oracle_run_pure (oracle : Oracle) {α : Type} (value : α) :
    fixedOracleRun oracle (pure value) = pure value := by
  simp [fixedOracleRun, oracle_run_pure]

theorem fixed_oracle_run_public (oracle : Oracle) {α : Type} (query : PublicSpec.Domain)
    (next : PublicSpec.Range query → OracleComp World α) :
    fixedOracleRun oracle ((liftM (World.query (.inr query)) : OracleComp World _) >>= next) =
      fixedOracleRun oracle (next (oracle.answer (m := Id) query)) := by
  rw [fixedOracleRun, oracle_run_public_bind]
  simp only [bind_pure_comp, Functor.map_map]
  rfl

theorem fixed_oracle_run_private (oracle : Oracle) {α : Type} (coins : unifSpec.Domain)
    (next : unifSpec.Range coins → OracleComp World α) :
    fixedOracleRun oracle ((liftM (World.query (.inl coins)) : OracleComp World _) >>= next) =
      (liftM (unifSpec.query coins) : ProbComp _) >>= fun answer => fixedOracleRun oracle (next answer) := by
  unfold fixedOracleRun
  change Prod.fst <$> oracle.run ((liftM (liftM (unifSpec.query coins) : ProbComp _) : OracleComp World _) >>= next) = _
  rw [oracle_run_coins_bind, map_bind]

/-- Marginalization also holds for a randomized continuation of the sampled table. -/
theorem compression_table_update_bind {α : Type} (input : CompressionSpec.Domain)
    (continuation : Compression → ProbComp α) :
    𝒟[do let answer ← $ᵗ (BitVec COMPRESSION_OUTPUT_LENGTH)
         let table ← $ᵗ Compression
         continuation (Function.update table input answer)] =
    𝒟[do let table ← $ᵗ Compression; continuation table] := by
  have marginal := evalDist_uniformSample_bind_update_map (R := (BitVec COMPRESSION_OUTPUT_LENGTH))
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample input (fun table : Compression => table)
  have marginal' :
      𝒟[do let answer ← $ᵗ (BitVec COMPRESSION_OUTPUT_LENGTH)
           let table ← $ᵗ Compression
           pure (Function.update table input answer)] = 𝒟[$ᵗ Compression] := by
    simpa only [bind_pure] using marginal
  calc
    _ = 𝒟[(do let answer ← $ᵗ (BitVec COMPRESSION_OUTPUT_LENGTH)
              let table ← $ᵗ Compression
              pure (Function.update table input answer)) >>= continuation] := by
      simp only [bind_assoc, pure_bind]
    _ = _ := by rw [evalDist_bind_of_discrete, marginal', ← evalDist_bind_of_discrete]

/-- Generalized lazy/eager equivalence: existing cached cells override the fresh
full table. In particular this supports repeated adaptive compression queries. -/
theorem compression_sampling_equivalence (permutation : Perm) {α : Type}
    (computation : OracleComp World α) (cache : CompressionCache) :
    𝒟[Prod.fst <$> compressionRun permutation computation cache] =
    𝒟[do let table ← $ᵗ Compression
         fixedOracleRun ⟨tableExtending cache table, permutation⟩ computation] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
    rw [compression_run_pure, map_pure]
    simp only [fixed_oracle_run_pure]
    exact (OracleComp.evalDist_bind_const ($ᵗ Compression) (pure value)).symm
  | query_bind query next ih =>
    rcases query with coins | publicQuery
    · rw [compression_run_private, map_bind]
      simp only [fixed_oracle_run_private]
      trans 𝒟[do let answer ← (liftM (unifSpec.query coins) : ProbComp _)
                 let table ← $ᵗ Compression
                 fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next answer)]
      · exact _root_.evalDist_bind_congr _ _ _ (fun answer => ih answer cache)
      · exact distribution_bind_comm _ _ _
    · simp only [fixed_oracle_run_public]
      rcases publicQuery with input | permQuery
      · rw [compression_run_compress]
        cases cached : cache input with
        | some answer =>
          rw [ih answer cache]
          apply _root_.evalDist_bind_congr
          intro table
          have reply : (Oracle.answer (m := Id) ⟨tableExtending cache table, permutation⟩ (.inl input)) = answer := by
            change (cache input).getD (table input) = answer
            rw [cached]
            rfl
          rw [reply]
        | none =>
          rw [map_bind]
          let continuation : Compression → ProbComp α := fun table =>
            fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next (tableExtending cache table input))
          trans 𝒟[do let answer ← $ᵗ (BitVec COMPRESSION_OUTPUT_LENGTH)
                     let table ← $ᵗ Compression
                     continuation (Function.update table input answer)]
          · apply _root_.evalDist_bind_congr
            intro answer
            rw [ih answer (cache.cacheQuery input answer)]
            apply _root_.evalDist_bind_congr
            intro table
            have updated := tableExtending_update_of_none cache table cached answer
            have reply : tableExtending cache (Function.update table input answer) input = answer := by
              simp [tableExtending, cached]
            simp only [continuation, reply, ← updated, tableExtending_cacheQuery]
          · exact compression_table_update_bind input continuation
      · rcases permQuery with input | input
        · rw [compression_run_permute]
          exact ih (permutation input) cache
        · rw [compression_run_inverse]
          exact ih (permutation.symm input) cache

/-- Starting from an empty compression cache gives exactly the fixed-table model
used by the contract, for any fixed permutation. -/
theorem compression_sampling_empty (permutation : Perm) {α : Type}
    (computation : OracleComp World α) :
    𝒟[Prod.fst <$> compressionRun permutation computation ∅] =
    𝒟[do let table ← $ᵗ Compression; fixedOracleRun ⟨table, permutation⟩ computation] := by
  rw [compression_sampling_equivalence]
  simp only [tableExtending_empty]

end CommitGolfCandidate
