import CommitGolfCandidate.LateHidingCell
import CommitGolfCandidate.LateHidingTree

/-! One hidden late-salt leaf is a fresh digest.

The leaf's final row holds two digests of its content and a 192-bit salt, so the
row itself depends on the oracle. The three unsalted calls are therefore run
first under lazy sampling: they add three entries to the cache and fix the two
digests. The final row is then a single cell keyed by a fresh hidden salt, and
`cached_salted_distance` applies. In the ideal game the three unsalted calls
have no effect on the continuation and are dropped again.

Loss: `(cached inputs + 3 + continuation calls) / 2^192`. The salt sits at
either end of the row according to the leaf's parity; only injectivity of the
row in its salt is used. -/
namespace CommitGolfCandidate.LateHiding

-- Observations retain the discrete measurable structure used by the contract.
local instance leafDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleSpec OracleComp.DeferredSampling

private theorem append_left_cancel {m n : Nat} {a c : BitVec m} {b : BitVec n}
    (same : a ++ b = c ++ b) : a = c := by
  simpa only [BitVec.extractLsb'_append_eq_left] using
    congrArg (fun x : BitVec (m+n) => x.extractLsb' n m) same

private theorem append_right_cancel {m n : Nat} {a : BitVec m} {b d : BitVec n}
    (same : a ++ b = a ++ d) : b = d := by
  simpa only [BitVec.extractLsb'_append_eq_right] using
    congrArg (fun x : BitVec (m+n) => x.extractLsb' 0 n) same

/-- The final row determines its salt at either parity. -/
theorem final_block_salt_injective (odd : Bool) (a b : Late.Digest) :
    Function.Injective fun salt : Late.Salt => Late.finalBlock odd salt a b := by
  intro first second same
  cases odd
  · have rows : first ++ (0 : BitVec 64) ++ b ++ a = second ++ (0 : BitVec 64) ++ b ++ a := same
    exact append_left_cancel (append_left_cancel (append_left_cancel rows))
  · have rows : b ++ a ++ (0 : BitVec 64) ++ first = b ++ a ++ (0 : BitVec 64) ++ second := same
    exact append_right_cancel rows

/-- A hidden leaf digest is a fresh uniform digest for every bounded continuation
that does not receive its salt, after any fixed cache of earlier answers. -/
theorem hidden_leaf_distance (permutation : Perm) (cache : CompressionCache)
    (keys : Finset Late.Block) (covered : ∀ input, cache input ≠ none → input ∈ keys)
    (odd : Bool) (value : Entry) {α : Type} (next : Late.Digest → OracleComp World α)
    (budget : Nat) (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ Late.Salt
          let oracle : Oracle := ⟨tableExtending cache table, permutation⟩
          fixedOracleRun oracle (next (leafDigest oracle.compression odd salt value)))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Late.Digest
          fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next answer)) ≤
      ((keys.card + 3 + budget : Nat) : ℝ) / 2^192 := by
  let lazyReal : ProbComp α := do
    let result ← compressionRun permutation (prehashM value) cache
    let table ← $ᵗ Compression
    let salt ← $ᵗ Late.Salt
    let oracle : Oracle := ⟨tableExtending result.2 table, permutation⟩
    fixedOracleRun oracle
      (next (oracle.compression (Late.finalBlock odd salt result.1.1 result.1.2)))
  let lazyIdeal : ProbComp α := do
    let result ← compressionRun permutation (prehashM value) cache
    let table ← $ᵗ Compression
    let answer ← $ᵗ Late.Digest
    fixedOracleRun ⟨tableExtending result.2 table, permutation⟩ (next answer)
  have real :
      𝒟[do let table ← $ᵗ Compression
           let salt ← $ᵗ Late.Salt
           let oracle : Oracle := ⟨tableExtending cache table, permutation⟩
           fixedOracleRun oracle (next (leafDigest oracle.compression odd salt value))] =
      𝒟[lazyReal] := by
    trans 𝒟[do let table ← $ᵗ Compression
                let salt ← $ᵗ Late.Salt
                fixedOracleRun ⟨tableExtending cache table, permutation⟩
                  (prehashM value >>= fun ab =>
                    Late.hash (Late.finalBlock odd salt ab.1 ab.2) >>= next)]
    · apply _root_.evalDist_bind_congr
      intro table
      apply _root_.evalDist_bind_congr
      intro salt
      rw [run_prehash, run_hash]
      rfl
    trans 𝒟[do let salt ← $ᵗ Late.Salt
                let table ← $ᵗ Compression
                fixedOracleRun ⟨tableExtending cache table, permutation⟩
                  (prehashM value >>= fun ab =>
                    Late.hash (Late.finalBlock odd salt ab.1 ab.2) >>= next)]
    · exact distribution_bind_comm _ _ _
    trans 𝒟[do let salt ← $ᵗ Late.Salt
                let result ← compressionRun permutation (prehashM value) cache
                let table ← $ᵗ Compression
                fixedOracleRun ⟨tableExtending result.2 table, permutation⟩
                  (Late.hash (Late.finalBlock odd salt result.1.1 result.1.2) >>= next)]
    · apply _root_.evalDist_bind_congr
      intro salt
      exact staged_sampling permutation cache (prehashM value)
        (fun ab => Late.hash (Late.finalBlock odd salt ab.1 ab.2) >>= next)
    trans 𝒟[do let result ← compressionRun permutation (prehashM value) cache
                let salt ← $ᵗ Late.Salt
                let table ← $ᵗ Compression
                fixedOracleRun ⟨tableExtending result.2 table, permutation⟩
                  (Late.hash (Late.finalBlock odd salt result.1.1 result.1.2) >>= next)]
    · exact distribution_bind_comm _ _ _
    · apply _root_.evalDist_bind_congr
      intro result
      trans 𝒟[do let table ← $ᵗ Compression
                  let salt ← $ᵗ Late.Salt
                  fixedOracleRun ⟨tableExtending result.2 table, permutation⟩
                    (Late.hash (Late.finalBlock odd salt result.1.1 result.1.2) >>= next)]
      · exact distribution_bind_comm _ _ _
      · apply _root_.evalDist_bind_congr
        intro table
        apply _root_.evalDist_bind_congr
        intro salt
        rw [run_hash]
  have ideal :
      𝒟[do let table ← $ᵗ Compression
           let answer ← $ᵗ Late.Digest
           fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next answer)] =
      𝒟[lazyIdeal] := by
    trans 𝒟[do let answer ← $ᵗ Late.Digest
                let table ← $ᵗ Compression
                fixedOracleRun ⟨tableExtending cache table, permutation⟩
                  (prehashM value >>= fun _ => next answer)]
    · trans 𝒟[do let answer ← $ᵗ Late.Digest
                  let table ← $ᵗ Compression
                  fixedOracleRun ⟨tableExtending cache table, permutation⟩ (next answer)]
      · exact distribution_bind_comm _ _ _
      · apply _root_.evalDist_bind_congr
        intro answer
        apply _root_.evalDist_bind_congr
        intro table
        rw [run_prehash]
    trans 𝒟[do let answer ← $ᵗ Late.Digest
                let result ← compressionRun permutation (prehashM value) cache
                let table ← $ᵗ Compression
                fixedOracleRun ⟨tableExtending result.2 table, permutation⟩ (next answer)]
    · apply _root_.evalDist_bind_congr
      intro answer
      exact staged_sampling permutation cache (prehashM value) (fun _ => next answer)
    trans 𝒟[do let result ← compressionRun permutation (prehashM value) cache
                let answer ← $ᵗ Late.Digest
                let table ← $ᵗ Compression
                fixedOracleRun ⟨tableExtending result.2 table, permutation⟩ (next answer)]
    · exact distribution_bind_comm _ _ _
    · apply _root_.evalDist_bind_congr
      intro result
      exact distribution_bind_comm _ _ _
  have distance : measureTVDist lazyReal lazyIdeal ≤
      ((keys.card + 3 + budget : Nat) : ℝ) / 2^192 := by
    unfold lazyReal lazyIdeal
    rw [bind_eq_attach_bind (compressionRun permutation (prehashM value) cache)]
    rw [bind_eq_attach_bind (compressionRun permutation (prehashM value) cache)]
    apply measureTVDist_bind_left_le_of_forall_le _ _ _ (by positivity)
    rintro ⟨result, reached⟩
    obtain ⟨known, size, covers⟩ := cache_covered permutation (prehashM value) 3
      (prehash_bound value) cache keys covered result reached
    have step := cached_salted_distance permutation result.2 known covers
      (fun salt : Late.Salt => Late.finalBlock odd salt result.1.1 result.1.2)
      (Function.invFun fun salt : Late.Salt => Late.finalBlock odd salt result.1.1 result.1.2)
      (Function.leftInverse_invFun (final_block_salt_injective odd result.1.1 result.1.2))
      next budget bounded
    refine step.trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (by omega : known.card + budget ≤ keys.card + 3 + budget)
  simpa only [measureTVDist, real, ideal] using distance

end CommitGolfCandidate.LateHiding
