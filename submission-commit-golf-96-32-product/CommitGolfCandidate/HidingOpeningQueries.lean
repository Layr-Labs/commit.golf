import CommitGolfCandidate.HidingHeapQueries

/-! An oracle continuation producing exactly the public root and opening bytes.
This query count is for the security reduction only; submitted machine cycles and
proof-size claims continue to use the existing exact proofs. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp

/-- The commitment and exact opening from one memoized heap computation: the heap
is computed once, the 64 chain calls follow, and the proof bytes are read from it. -/
def queryTranscript (heap : OracleComp World (Nat → Digest)) (salt : Index → Digest)
    (positions : Positions) : OracleComp World (Commitment × Proof) := do
  let values ← heap
  let root ← hashBlocks (capBlocks (referenceCap values)) 0
  pure (root, referenceOpening values salt positions)

theorem query_transcript_bound (heap : OracleComp World (Nat → Digest)) (budget : Nat)
    (bounded : PublicQueryBound heap budget) (salt : Index → Digest) (positions : Positions) :
    PublicQueryBound (queryTranscript heap salt positions) (budget+64) := by
  have chain (values : Nat → Digest) :=
    public_query_bound_bind (hash_blocks_bound (capBlocks (referenceCap values)) 0)
      (fun root => (show PublicQueryBound
        (pure (root, referenceOpening values salt positions) : OracleComp World _) 0 from trivial))
  simp only [capBlocks, List.length_map, List.length_range, Nat.add_zero] at chain
  exact public_query_bound_bind bounded chain

theorem query_transcript_reference (oracle : Oracle) (heap : OracleComp World (Nat → Digest))
    (values : Nat → Digest) (exact : fixedOracleRun oracle heap = pure values)
    (salt : Index → Digest) (positions : Positions) :
    fixedOracleRun oracle (queryTranscript heap salt positions) =
      pure (capRoot oracle.compression (referenceCap values), referenceOpening values salt positions) := by
  rw [queryTranscript, fixed_oracle_run_bind, exact, pure_bind, fixed_hash_blocks, fixed_oracle_run_pure]
  rfl

end CommitGolfCandidate
