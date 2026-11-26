import CommitGolfCandidate.HidingOpeningQueries
import CommitGolfCandidate.HidingStages
import CommitGolfCandidate.HidingLeaf

/-! Isolate one unopened leaf's 256-bit initial digest inside the hybrid root-and-opening
continuation, and provide the actual tagged leaf oracle program for `HidingGameIntegration`. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleComp.DeferredSampling

theorem opening_index_mem (positions : Positions) (ordinal : Nat)
    (present : ordinal < positions.card) :
    (⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩ : Index) ∈ positions := by
  have indexEq : (⟨openingIndex positions ordinal, opening_index_bound positions ordinal⟩ : Index) =
      (positions.sort (· ≤ ·))[ordinal]'(by simpa using present) := by
    apply Fin.ext
    simp only [openingIndex, dif_pos present]
  rw [indexEq]
  have member := List.getElem_mem (l := positions.sort (· ≤ ·))
    (n := ordinal) (by simpa using present)
  simpa only [Finset.mem_sort] using member

/-- The serialized proof reads 16-byte salts only at the positions actually opened. -/
theorem reference_opening_salt_congr (heap : Nat → Digest) (left right : Index → Salt)
    (positions : Positions) (agree : ∀ index ∈ positions, left index = right index) :
    referenceOpening heap left positions = referenceOpening heap right positions := by
  unfold referenceOpening
  apply List.map_congr_left
  intro offset member
  have below : offset < openingProofBytes positions.card := List.mem_range.mp member
  unfold referenceOpeningByte
  by_cases batch : positions.card = BATCH
  · rw [if_pos batch, if_pos batch]
    by_cases inRecs : offset < 71680
    · rw [if_pos inRecs, if_pos inRecs]
      dsimp only
      split
      · have present : offset / 560 < positions.card := by
          rw [batch]; change offset / 560 < 128; omega
        rw [agree _ (opening_index_mem positions _ present)]
      · rfl
    · rw [if_neg inRecs, if_neg inRecs]
  · rw [if_neg batch, if_neg batch]
    have belowNorm : offset < 784 * positions.card := by
      simp only [openingProofBytes, if_neg batch] at below; exact below
    have present : offset / 784 < positions.card := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
    dsimp only
    split
    · rw [agree _ (opening_index_mem positions _ present)]
    · rfl

/-- Oracle program computing an honest position-tagged salted leaf (4 queries). -/
def queryActualLeaf (message : Message) (salt : Index → Salt) (index : Nat) : OracleComp World Digest :=
  if inside : index < LENGTH then do
    let idx : Index := ⟨index, inside⟩
    let d0 ← (liftM (World.query (.inr (.inl (leafInitInput idx (salt idx) (message idx))))) : OracleComp World Digest)
    hashBlocks (leafTailBlocks (message idx)) d0
  else pure 0

def actualLeafValues (compress : Compression) (message : Message) (salt : Index → Salt)
    (index : Nat) : Digest :=
  if inside : index < LENGTH then
    leafDigest compress ⟨index, inside⟩ (salt ⟨index, inside⟩) (message ⟨index, inside⟩)
  else 0

theorem query_actual_leaf_reference (oracle : Oracle) (message : Message) (salt : Index → Salt)
    (index : Nat) : fixedOracleRun oracle (queryActualLeaf message salt index) =
      pure (actualLeafValues oracle.compression message salt index) := by
  unfold queryActualLeaf actualLeafValues
  split
  · rename_i inside
    dsimp only
    erw [fixed_oracle_run_public]
    have result := fixed_hash_blocks oracle (leafTailBlocks (message ⟨index, inside⟩))
      (oracle.compression (leafInitInput ⟨index, inside⟩ (salt ⟨index, inside⟩) (message ⟨index, inside⟩))) pure
    simp only [bind_pure, fixed_oracle_run_pure] at result
    exact result
  · exact fixed_oracle_run_pure _ _

/-- Oracle program computing a hybrid leaf: opened leaves use `queryActualLeaf`, unopened
leaves start the 3-block tail chain from `freshInit`. -/
def queryHybridLeaf (positions : Positions) (message : Message) (salt : Index → Salt)
    (freshInit : Index → Digest) (index : Nat) : OracleComp World Digest :=
  if inside : index < LENGTH then
    let idx : Index := ⟨index, inside⟩
    if idx ∈ positions then do
      let d0 ← (liftM (World.query (.inr (.inl (leafInitInput idx (salt idx) (message idx))))) : OracleComp World Digest)
      hashBlocks (leafTailBlocks (message idx)) d0
    else
      hashBlocks (leafTailBlocks (message idx)) (freshInit idx)
  else pure 0

def queryHybridLeafExcept (positions : Positions) (message : Message) (salt : Index → Salt)
    (freshInit : Index → Digest) (hidden : Index) (digest : Digest) (index : Nat) :
    OracleComp World Digest :=
  if index = hidden.val then pure digest else queryHybridLeaf positions message salt freshInit index

def hybridLeafValues (compress : Compression) (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest) (index : Nat) : Digest :=
  if inside : index < LENGTH then
    hybridLeafDigest compress positions message salt freshInit ⟨index, inside⟩
  else 0

def hybridLeafValuesExcept (compress : Compression) (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest) (hidden : Index)
    (digest : Digest) (index : Nat) : Digest :=
  if index = hidden.val then digest else hybridLeafValues compress positions message salt freshInit index

theorem query_hybrid_leaf_bound (positions : Positions) (message : Message) (salt : Index → Salt)
    (freshInit : Index → Digest) (index : Nat) :
    PublicQueryBound (queryHybridLeaf positions message salt freshInit index) 8 := by
  unfold queryHybridLeaf
  split
  · dsimp only
    split
    · change 1 ≤ 8 ∧ ∀ answer, PublicQueryBound (hashBlocks (leafTailBlocks _) answer) (8 - 1)
      refine ⟨by decide, fun answer => ?_⟩
      apply PublicQueryBound.mono (hash_blocks_bound _ _)
      simp [leafTailBlocks]
    · apply PublicQueryBound.mono (hash_blocks_bound _ _)
      simp [leafTailBlocks]
  · trivial

theorem query_hybrid_leaf_except_bound (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest)
    (hidden : Index) (digest : Digest) (index : Nat) :
    PublicQueryBound (queryHybridLeafExcept positions message salt freshInit hidden digest index) 8 := by
  unfold queryHybridLeafExcept
  split
  · trivial
  · exact query_hybrid_leaf_bound positions message salt freshInit index

theorem query_hybrid_leaf_reference (oracle : Oracle) (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest) (index : Nat) :
    fixedOracleRun oracle (queryHybridLeaf positions message salt freshInit index) =
      pure (hybridLeafValues oracle.compression positions message salt freshInit index) := by
  unfold queryHybridLeaf hybridLeafValues hybridLeafDigest
  split
  · rename_i inside
    dsimp only
    split
    · erw [fixed_oracle_run_public]
      have result := fixed_hash_blocks oracle (leafTailBlocks (message ⟨index, inside⟩))
        (oracle.compression (leafInitInput ⟨index, inside⟩ (salt ⟨index, inside⟩) (message ⟨index, inside⟩))) pure
      simp only [bind_pure, fixed_oracle_run_pure] at result
      exact result
    · have result := fixed_hash_blocks oracle (leafTailBlocks (message ⟨index, inside⟩))
        (freshInit ⟨index, inside⟩) pure
      simpa only [bind_pure, fixed_oracle_run_pure, leafDigestFromInit] using result
  · exact fixed_oracle_run_pure _ _

theorem query_hybrid_leaf_except_reference (oracle : Oracle) (positions : Positions)
    (message : Message) (salt : Index → Salt) (freshInit : Index → Digest)
    (hidden : Index) (digest : Digest) (index : Nat) :
    fixedOracleRun oracle (queryHybridLeafExcept positions message salt freshInit hidden digest index) =
      pure (hybridLeafValuesExcept oracle.compression positions message salt freshInit hidden digest index) := by
  unfold queryHybridLeafExcept hybridLeafValuesExcept
  split
  · exact fixed_oracle_run_pure _ _
  · exact query_hybrid_leaf_reference oracle positions message salt freshInit index

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

/-- Restoring an unopened leaf's 3-block digest gives precisely the hybrid tree for the
updated message and fresh 256-bit initial digest. -/
theorem hybrid_leaf_values_except_update (compress : Compression) (positions : Positions)
    (message : Message) (salt : Index → Salt) (freshInit : Index → Digest)
    (hidden : Index) (unopened : hidden ∉ positions) (value : Entry) (fresh : Digest) :
    hybridLeafValuesExcept compress positions message salt freshInit hidden
      (leafDigestFromInit compress fresh value) =
    hybridLeafValues compress positions (Function.update message hidden value)
      salt (Function.update freshInit hidden fresh) := by
  funext index
  unfold hybridLeafValuesExcept hybridLeafValues hybridLeafDigest
  by_cases same : index = hidden.val
  · subst index
    simp only [dif_pos hidden.isLt, if_true, unopened, if_false, Function.update_self]
  · rw [if_neg same]
    split
    · rename_i inside
      have different : (⟨index, inside⟩ : Index) ≠ hidden := by
        intro equal
        exact same (congrArg Fin.val equal)
      rw [Function.update_of_ne different, Function.update_of_ne different]
    · rfl

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

end CommitGolfCandidate
