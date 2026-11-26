import CommitGolfCandidate.HidingLeafReplacement

import CommitGolfCandidate.TruncHidingHeapQueries

namespace CommitGolfCandidate.Trunc

open CommitGolf OracleComp OracleComp.DeferredSampling

set_option maxRecDepth 12000

set_option maxHeartbeats 800000

def queryHybridTranscriptExcept (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest)
    (hidden : Index) (digest : Digest) : OracleComp World (Commitment × Proof) :=
  queryTranscript (queryHeap LENGTH (queryHybridLeafExcept positions message salt freshInit hidden digest) LOG_LENGTH)
    salt positions

attribute [local irreducible] heapQueryBudget queryHeap queryTranscript

theorem query_hybrid_transcript_except_bound (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest) (hidden : Index) (digest : Digest) :
    PublicQueryBound (queryHybridTranscriptExcept positions message salt freshInit hidden digest)
      ((1 + 784 * positions.card) * heapQueryBudget 8 LOG_LENGTH) := by
  unfold queryHybridTranscriptExcept
  apply query_transcript_bound
  intro node
  exact query_heap_bound LENGTH _ 8
    (query_hybrid_leaf_except_bound positions message salt freshInit hidden digest) LOG_LENGTH node

theorem query_hybrid_transcript_except_reference (oracle : Oracle) (positions : Positions)
    (message : Message) (salt : Index → Salt) (freshInit : Index → Digest)
    (hidden : Index) (digest : Digest) :
    fixedOracleRun oracle (queryHybridTranscriptExcept positions message salt freshInit hidden digest) =
      let heap := referenceHeap oracle.compression LENGTH
        (hybridLeafValuesExcept oracle.compression positions message salt freshInit hidden digest)
      pure (heap 1, referenceOpening heap salt positions) := by
  apply query_transcript_reference
  intro node positive inside
  apply query_heap_reference oracle LENGTH _ _
    (query_hybrid_leaf_except_reference oracle positions message salt freshInit hidden digest)
    LOG_LENGTH node positive inside
  change LENGTH ≤ LENGTH * node
  have larger := Nat.mul_le_mul_left LENGTH positive
  simpa only [Nat.mul_one] using larger

theorem query_hybrid_transcript_hidden_update (oracle : Oracle) (positions : Positions)
    (message : Message) (salt : Index → Salt) (freshInit : Index → Digest)
    (hidden : Index) (unopened : hidden ∉ positions) (value : Entry) (fresh : Digest) :
    fixedOracleRun oracle
      (queryHybridTranscriptExcept positions message salt freshInit hidden
        (leafDigestFromInit oracle.compression fresh value)) =
      pure (hybridTranscript oracle.compression positions
        (Function.update message hidden value) salt (Function.update freshInit hidden fresh)) := by
  rw [query_hybrid_transcript_except_reference,
    hybrid_leaf_values_except_update oracle.compression positions message salt freshInit hidden unopened value fresh]
  rfl

end CommitGolfCandidate.Trunc
