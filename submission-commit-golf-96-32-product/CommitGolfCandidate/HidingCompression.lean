import CommitGolfCandidate.Probability
import CommitGolfCandidate.HidingHiddenQuery

/-! A hidden salted compression output can be replaced by a fresh digest. The
continuation retains adaptive access to the same compression and permutation.
These lemmas concern a fresh table; conditioning on an earlier query transcript
requires the separate cache argument before applying them to the full game. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingCompressionDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf OracleComp OracleComp.DeferredSampling

/-- Sampling the answer first and programming its cell gives the exact joint
distribution of a uniform table and its answer, including a randomized observer. -/
theorem compression_answer_programming (permutation : Perm) (input : BitVec COMPRESSION_INPUT_LENGTH)
    {α : Type} (next : Digest → OracleComp World α) :
    𝒟[do let answer ← $ᵗ Digest
         let table ← $ᵗ Compression
         fixedOracleRun (programCompression ⟨table, permutation⟩ input answer) (next answer)] =
    𝒟[do let table ← $ᵗ Compression
         fixedOracleRun ⟨table, permutation⟩ (next (table input))] := by
  trans 𝒟[do let answer ← $ᵗ Digest
              let table ← $ᵗ Compression
              fixedOracleRun ⟨Function.update table input answer, permutation⟩
                (next ((Function.update table input answer) input))]
  · apply _root_.evalDist_bind_congr
    intro answer
    apply _root_.evalDist_bind_congr
    intro table
    erw [Function.update_self]
    rfl
  · exact compression_table_update_bind input (fun table =>
      fixedOracleRun ⟨table, permutation⟩ (next (table input)))

/-- Exact intermediate game: a uniform hidden salt and an independent digest,
with the digest programmed at the corresponding salted compression input. -/
theorem salted_compression_programming (permutation : Perm) (block : LeafBlock)
    {α : Type} (next : Digest → OracleComp World α) :
    𝒟[do let salt ← $ᵗ Digest
         let answer ← $ᵗ Digest
         let table ← $ᵗ Compression
         fixedOracleRun (programCompression ⟨table, permutation⟩ ((leafInput salt block)) answer)
           (next answer)] =
    𝒟[do let table ← $ᵗ Compression
         let salt ← $ᵗ Digest
         fixedOracleRun ⟨table, permutation⟩ (next (absorb table salt block))] := by
  trans 𝒟[do let salt ← $ᵗ Digest
              let table ← $ᵗ Compression
              fixedOracleRun ⟨table, permutation⟩ (next (absorb table salt block))]
  · exact _root_.evalDist_bind_congr _ _ _ (fun salt =>
      compression_answer_programming permutation ((leafInput salt block)) next)
  · exact distribution_bind_comm _ _ _

/-- A salted compression output hides its block against a bounded adaptive
continuation, at cost q/2^256. The salt is private; the output is public. -/
theorem salted_compression_distance (permutation : Perm) (block : LeafBlock)
    {α : Type} (next : Digest → OracleComp World α) (budget : Nat)
    (bounded : ∀ answer, PublicQueryBound (next answer) budget) :
    measureTVDist
      (do let table ← $ᵗ Compression
          let salt ← $ᵗ Digest
          fixedOracleRun ⟨table, permutation⟩ (next (absorb table salt block)))
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
    fixedOracleRun (programCompression ⟨table, permutation⟩ ((leafInput salt block)) answer)
      (next answer)
  have distance : measureTVDist ideal programmed ≤ ((budget : ENNReal) / 2^256).toReal := by
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ Digest) _ _ (by positivity)
    intro answer
    apply measureTVDist_bind_left_le_of_forall_le ($ᵗ Compression) _ _ (by positivity)
    intro table
    exact hidden_reprogram_distance ⟨table, permutation⟩ block answer (next answer)
      budget (bounded answer)
  have ideal_eq : 𝒟[ideal] =
      𝒟[do let table ← $ᵗ Compression
           let answer ← $ᵗ Digest
           fixedOracleRun ⟨table, permutation⟩ (next answer)] := by
    unfold ideal
    trans 𝒟[do let answer ← $ᵗ Digest
                let table ← $ᵗ Compression
                fixedOracleRun ⟨table, permutation⟩ (next answer)]
    · apply _root_.evalDist_bind_congr
      intro answer
      apply _root_.evalDist_bind_congr
      intro table
      exact OracleComp.evalDist_bind_const _ _
    · exact distribution_bind_comm _ _ _
  have programmed_eq : 𝒟[programmed] =
      𝒟[do let table ← $ᵗ Compression
           let salt ← $ᵗ Digest
           fixedOracleRun ⟨table, permutation⟩ (next (absorb table salt block))] := by
    unfold programmed
    trans 𝒟[do let salt ← $ᵗ Digest
                let answer ← $ᵗ Digest
                let table ← $ᵗ Compression
                fixedOracleRun (programCompression ⟨table, permutation⟩ ((leafInput salt block)) answer)
                  (next answer)]
    · trans 𝒟[do let answer ← $ᵗ Digest
                  let salt ← $ᵗ Digest
                  let table ← $ᵗ Compression
                  fixedOracleRun (programCompression ⟨table, permutation⟩ ((leafInput salt block)) answer)
                    (next answer)]
      · exact _root_.evalDist_bind_congr _ _ _ (fun _ => distribution_bind_comm _ _ _)
      · exact distribution_bind_comm _ _ _
    · exact salted_compression_programming permutation block next
  rw [measureTVDist_comm] at distance
  simpa only [measureTVDist, ideal_eq, programmed_eq] using distance

end CommitGolfCandidate
