import CommitGolfCandidate.HidingOpeningQueries

namespace CommitGolfCandidate
open CommitGolf OracleComp
set_option maxHeartbeats 1000000

def queryLeafCache (offset : Nat) (leaf : Nat → OracleComp World Digest) :
    Nat → (Nat → Digest) → OracleComp World (Nat → Digest)
  | 0, heap => pure heap
  | count+1, heap => do
      let value ← leaf count
      queryLeafCache offset leaf count (Function.update heap (offset+count) value)

def leafCache (offset : Nat) (leaf : Nat → Digest) : Nat → (Nat → Digest) → (Nat → Digest)
  | 0, heap => heap
  | count+1, heap => leafCache offset leaf count (Function.update heap (offset+count) (leaf count))

theorem query_leaf_cache_bound (offset : Nat) (leaf : Nat → OracleComp World Digest)
    (budget : Nat) (bounded : ∀ index, PublicQueryBound (leaf index) budget)
    (count : Nat) (heap : Nat → Digest) :
    PublicQueryBound (queryLeafCache offset leaf count heap) (count*budget) := by
  induction count generalizing heap with
  | zero => trivial
  | succ count ih =>
    have run := public_query_bound_bind (bounded count) (fun value => ih (Function.update heap (offset+count) value))
    simpa only [queryLeafCache,Nat.succ_mul,Nat.add_comm] using run

theorem query_leaf_cache_reference (oracle : Oracle) (offset : Nat)
    (leaf : Nat → OracleComp World Digest) (values : Nat → Digest)
    (correct : ∀ index, fixedOracleRun oracle (leaf index)=pure (values index))
    (count : Nat) (heap : Nat → Digest) :
    fixedOracleRun oracle (queryLeafCache offset leaf count heap)=pure (leafCache offset values count heap) := by
  induction count generalizing heap with
  | zero => exact fixed_oracle_run_pure _ _
  | succ count ih =>
    rw [queryLeafCache,fixed_oracle_run_bind,correct,pure_bind,ih]
    rfl

theorem leaf_cache_apply (offset : Nat) (values : Nat → Digest) (count : Nat)
    (heap : Nat → Digest) (node : Nat) :
    leafCache offset values count heap node=
      if offset≤node ∧ node<offset+count then values (node-offset) else heap node := by
  induction count generalizing heap with
  | zero => simp [leafCache]
  | succ count ih =>
    rw [leafCache,ih]
    by_cases lower : offset≤node
    · by_cases upper : node<offset+count
      · simp [lower,upper,show node<offset+(count+1) by omega]
      · by_cases equal : node=offset+count
        · subst node
          simp [show ¬offset+count<offset+count by omega,Function.update_self]
        · have outside : ¬node<offset+(count+1) := by omega
          simp [lower,upper,equal,outside,Function.update_of_ne equal]
    · have unequal : node≠offset+count := by omega
      simp [lower,Function.update_of_ne unequal]

def queryParentCache : Nat → (Nat → Digest) → OracleComp World (Nat → Digest)
  | 0, heap => pure heap
  | count+1, heap => do
      let value ← hashBlocks [heap (2*(count+1)+1)] (heap (2*(count+1)))
      queryParentCache count (Function.update heap (count+1) value)

def parentCache (compression : Compression) : Nat → (Nat → Digest) → (Nat → Digest)
  | 0, heap => heap
  | count+1, heap => parentCache compression count
      (Function.update heap (count+1) (combine compression (heap (2*(count+1))) (heap (2*(count+1)+1))))

theorem query_parent_cache_bound (count : Nat) (heap : Nat → Digest) :
    PublicQueryBound (queryParentCache count heap) count := by
  induction count generalizing heap with
  | zero => trivial
  | succ count ih =>
    have run := public_query_bound_bind (hash_blocks_bound [heap (2*(count+1)+1)] (heap (2*(count+1))))
      (fun value => ih (Function.update heap (count+1) value))
    simpa only [queryParentCache,List.length_singleton,Nat.add_comm] using run

theorem query_parent_cache_reference (oracle : Oracle) (count : Nat) (heap : Nat → Digest) :
    fixedOracleRun oracle (queryParentCache count heap)=pure (parentCache oracle.compression count heap) := by
  induction count generalizing heap with
  | zero => exact fixed_oracle_run_pure _ _
  | succ count ih =>
    rw [queryParentCache,fixed_oracle_run_bind]
    have hashed := fixed_hash_blocks oracle [heap (2*(count+1)+1)] (heap (2*(count+1))) pure
    simp only [bind_pure,List.foldl_cons,List.foldl_nil,fixed_oracle_run_pure] at hashed
    rw [hashed,pure_bind,ih]
    rfl

theorem parent_cache_correct (compression : Compression) (leafCount count : Nat)
    (values : Nat → Digest) (heap : Nat → Digest) (bounded : count<leafCount)
    (ready : ∀ node, count<node → node<2*leafCount →
      heap node=referenceHeap compression leafCount values node) :
    ∀ node, 0<node → node<2*leafCount →
      parentCache compression count heap node=referenceHeap compression leafCount values node := by
  induction count generalizing heap with
  | zero => exact ready
  | succ count ih =>
    rw [parentCache]
    apply ih (Function.update heap (count+1)
      (combine compression (heap (2*(count+1))) (heap (2*(count+1)+1)))) (by omega)
    intro node greater inside
    by_cases equal : node=count+1
    · subst node
      rw [Function.update_self,ready _ (by omega) (by omega),ready _ (by omega) (by omega)]
      exact (reference_heap_parent compression leafCount values (count+1) (by omega) bounded).symm
    · rw [Function.update_of_ne equal]
      exact ready node (by omega) inside

theorem parent_cache_outside (compression : Compression) (count : Nat)
    (heap : Nat → Digest) (node : Nat) (outside : node=0 ∨ count<node) :
    parentCache compression count heap node=heap node := by
  induction count generalizing heap with
  | zero => rfl
  | succ count ih =>
    rw [parentCache,ih _ (by omega),Function.update_of_ne (show node≠count+1 by omega)]

def queryWholeCache (leafCount : Nat) (leaf : Nat → OracleComp World Digest) :
    OracleComp World (Nat → Digest) := do
  let heap ← queryLeafCache leafCount leaf leafCount (fun _ => 0)
  queryParentCache (leafCount-1) heap

def wholeCache (compression : Compression) (leafCount : Nat) (values : Nat → Digest) : Nat → Digest :=
  parentCache compression (leafCount-1) (leafCache leafCount values leafCount (fun _ => 0))

theorem query_whole_cache_bound (leafCount : Nat) (leaf : Nat → OracleComp World Digest)
    (budget : Nat) (bounded : ∀ index, PublicQueryBound (leaf index) budget) :
    PublicQueryBound (queryWholeCache leafCount leaf) (leafCount*budget+(leafCount-1)) :=
  public_query_bound_bind (query_leaf_cache_bound leafCount leaf budget bounded leafCount _)
    (fun heap => query_parent_cache_bound (leafCount-1) heap)

theorem query_whole_cache_reference (oracle : Oracle) (leafCount : Nat)
    (leaf : Nat → OracleComp World Digest) (values : Nat → Digest)
    (correct : ∀ index, fixedOracleRun oracle (leaf index)=pure (values index)) :
    fixedOracleRun oracle (queryWholeCache leafCount leaf)=pure (wholeCache oracle.compression leafCount values) := by
  rw [queryWholeCache,fixed_oracle_run_bind,query_leaf_cache_reference oracle leafCount leaf values correct,
    pure_bind,query_parent_cache_reference]
  rfl

theorem whole_cache_reference (compression : Compression) (leafCount : Nat)
    (positive : 0<leafCount) (values : Nat → Digest) :
    wholeCache compression leafCount values=referenceHeap compression leafCount values := by
  funext node
  by_cases valid : 0<node ∧ node<2*leafCount
  · apply parent_cache_correct compression leafCount (leafCount-1) values _ (by omega) _ node valid.1 valid.2
    intro index greater inside
    rw [leaf_cache_apply,if_pos (by omega)]
    have address : leafCount+(index-leafCount)=index := by omega
    rw [←address,reference_heap_leaf _ _ _ _ (by omega),Nat.add_sub_cancel_left]
  · unfold wholeCache
    rw [parent_cache_outside compression (leafCount-1) _ node (by omega),leaf_cache_apply,if_neg (by omega)]
    rw [referenceHeap,dif_neg (by omega),if_neg (by omega)]

def querySharedTranscript (leafCount : Nat) (leaf : Nat → OracleComp World Digest)
    (salt : Index → Digest) (positions : Positions) : OracleComp World (Commitment × Proof) := do
  let heap ← queryWholeCache leafCount leaf
  pure (heap 1,referenceOpening heap salt positions)

theorem query_shared_transcript_bound (leafCount : Nat) (leaf : Nat → OracleComp World Digest)
    (budget : Nat) (bounded : ∀ index, PublicQueryBound (leaf index) budget)
    (salt : Index → Digest) (positions : Positions) :
    PublicQueryBound (querySharedTranscript leafCount leaf salt positions) (leafCount*budget+(leafCount-1)) := by
  have run := public_query_bound_bind (query_whole_cache_bound leafCount leaf budget bounded)
    (fun heap => (show PublicQueryBound
      (pure (heap 1,referenceOpening heap salt positions) : OracleComp World (Commitment × Proof)) 0 from trivial))
  simpa only [querySharedTranscript,Nat.add_zero] using run

theorem query_shared_transcript_reference (oracle : Oracle) (leafCount : Nat) (positive : 0<leafCount)
    (leaf : Nat → OracleComp World Digest) (values : Nat → Digest)
    (correct : ∀ index, fixedOracleRun oracle (leaf index)=pure (values index))
    (salt : Index → Digest) (positions : Positions) :
    fixedOracleRun oracle (querySharedTranscript leafCount leaf salt positions)=
      let heap := referenceHeap oracle.compression leafCount values
      pure (heap 1,referenceOpening heap salt positions) := by
  rw [querySharedTranscript,fixed_oracle_run_bind,
    query_whole_cache_reference oracle leafCount leaf values correct,pure_bind,
    whole_cache_reference oracle.compression leafCount positive values,fixed_oracle_run_pure]
  rfl


end CommitGolfCandidate
