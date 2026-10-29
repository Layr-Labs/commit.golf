import CommitGolfCandidate.HidingHiddenQuery

/-! A hidden salted compression output can be replaced by a fresh digest. The
continuation retains adaptive access to the same compression and permutation.
These lemmas concern a fresh table; conditioning on an earlier query transcript
requires the separate cache argument before applying them to the full game. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleComp.DeferredSampling

/-- Sampling the answer first and programming its cell gives the exact joint
distribution of a uniform table and its answer, including a randomized observer. -/
theorem compression_answer_programming (permutation : Perm) (input : BitVec 512)
    {α : Type} (next : Digest → OracleComp World α) :
    𝒮[do let answer ← $ᵗ Digest
         let table ← $ᵗ Compression
         fixedOracleRun (programCompression ⟨table, permutation⟩ input answer) (next answer)] =
    𝒮[do let table ← $ᵗ Compression
         fixedOracleRun ⟨table, permutation⟩ (next (table input))] := by
  trans 𝒮[do let answer ← $ᵗ Digest
              let table ← $ᵗ Compression
              fixedOracleRun ⟨Function.update table input answer, permutation⟩
                (next ((Function.update table input answer) input))]
  · apply evalSPMF_bind_congr_left
    intro answer
    apply evalSPMF_bind_congr_left
    intro table
    erw [Function.update_self]
    rfl
  · exact compression_table_update_bind input (fun table =>
      fixedOracleRun ⟨table, permutation⟩ (next (table input)))

/-- Exact intermediate game: a uniform hidden salt and an independent digest,
with the digest programmed at the corresponding salted compression input. -/
theorem salted_compression_programming (permutation : Perm) (block : Digest)
    {α : Type} (next : Digest → OracleComp World α) :
    𝒮[do let salt ← $ᵗ Digest
         let answer ← $ᵗ Digest
         let table ← $ᵗ Compression
         fixedOracleRun (programCompression ⟨table, permutation⟩ (block ++ salt) answer)
           (next answer)] =
    𝒮[do let table ← $ᵗ Compression
         let salt ← $ᵗ Digest
         fixedOracleRun ⟨table, permutation⟩ (next (combine table salt block))] := by
  trans 𝒮[do let salt ← $ᵗ Digest
              let table ← $ᵗ Compression
              fixedOracleRun ⟨table, permutation⟩ (next (combine table salt block))]
  · exact evalSPMF_bind_congr_left _ _ _ (fun salt =>
      compression_answer_programming permutation (block ++ salt) next)
  · exact evalSPMF_bind_comm _ _ _

/-- A salted compression output hides its block against a bounded adaptive
continuation, at cost q/2^256. The salt is private; the output is public. -/
theorem salted_compression_distance (permutation : Perm) (block : Digest)
    {α : Type} (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    tvDist
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ Digest
          fixedOracleRun ⟨table, permutation⟩ (next (combine table salt block)))
      (do let table ← $ᵗ Compression
          let answer ← $ᵗ Digest
          fixedOracleRun ⟨table, permutation⟩ (next answer)) ≤
      ((budget : ENNReal) / 2^256).toReal := by
  let ideal : ProbComp α := do
    let answer ← $ᵗ Digest
    let table ← $ᵗ Compression
    let _salt ← $ᵗ Digest
    fixedOracleRun ⟨table, permutation⟩ (next answer)
  let programmed : ProbComp α := do
    let answer ← $ᵗ Digest
    let table ← $ᵗ Compression
    let salt ← $ᵗ Digest
    fixedOracleRun (programCompression ⟨table, permutation⟩ (block ++ salt) answer)
      (next answer)
  have distance : tvDist ideal programmed ≤ ((budget : ENNReal) / 2^256).toReal := by
    apply tvDist_bind_left_le_const' ($ᵗ Digest)
    intro answer
    apply tvDist_bind_left_le_const' ($ᵗ Compression)
    intro table
    exact hidden_reprogram_distance ⟨table, permutation⟩ block answer (next answer)
      budget (bounded answer)
  have ideal_eq : 𝒮[ideal] =
      𝒮[do let table ← $ᵗ Compression
           let answer ← $ᵗ Digest
           fixedOracleRun ⟨table, permutation⟩ (next answer)] := by
    unfold ideal
    trans 𝒮[do let answer ← $ᵗ Digest
                let table ← $ᵗ Compression
                fixedOracleRun ⟨table, permutation⟩ (next answer)]
    · apply evalSPMF_bind_congr_left
      intro answer
      apply evalSPMF_bind_congr_left
      intro table
      exact evalSPMF_bind_const_neverFails _ (by simp) _
    · exact evalSPMF_bind_comm _ _ _
  have programmed_eq : 𝒮[programmed] =
      𝒮[do let table ← $ᵗ Compression
           let salt ← $ᵗ Digest
           fixedOracleRun ⟨table, permutation⟩ (next (combine table salt block))] := by
    unfold programmed
    trans 𝒮[do let salt ← $ᵗ Digest
                let answer ← $ᵗ Digest
                let table ← $ᵗ Compression
                fixedOracleRun (programCompression ⟨table, permutation⟩ (block ++ salt) answer)
                  (next answer)]
    · trans 𝒮[do let answer ← $ᵗ Digest
                  let salt ← $ᵗ Digest
                  let table ← $ᵗ Compression
                  fixedOracleRun (programCompression ⟨table, permutation⟩ (block ++ salt) answer)
                    (next answer)]
      · exact evalSPMF_bind_congr_left _ _ _ (fun _ => evalSPMF_bind_comm _ _ _)
      · exact evalSPMF_bind_comm _ _ _
    · exact salted_compression_programming permutation block next
  rw [tvDist_comm] at distance
  simpa only [tvDist, ideal_eq, programmed_eq] using distance

end CommitGolfCandidate
