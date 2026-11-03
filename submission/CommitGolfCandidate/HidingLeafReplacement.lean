import CommitGolfCandidate.HidingOpeningQueries
import CommitGolfCandidate.HidingStages

/-! Isolate one unopened leaf inside the full root-and-opening continuation.
Its salt is absent from the public proof, and the continuation uses that leaf only
through the supplied digest. All other leaves retain their actual oracle hashes. -/
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

/-- The serialized proof reads salts only at the positions actually opened. -/
theorem reference_opening_salt_congr (heap : Nat → Digest) (left right : Index → Digest)
    (positions : Positions) (agree : ∀ index ∈ positions, left index = right index) :
    referenceOpening heap left positions = referenceOpening heap right positions := by
  unfold referenceOpening
  apply List.map_congr_left
  intro offset member
  have below := List.mem_range.mp member
  have present : offset/800 < positions.card := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
  unfold referenceOpeningDigest
  split
  · rw [agree _ (opening_index_mem positions _ present)]
  · rfl

theorem reference_opening_hidden_salt (heap : Nat → Digest) (salt : Index → Digest)
    (positions : Positions) (hidden : Index) (unopened : hidden ∉ positions) (fresh : Digest) :
    referenceOpening heap (Function.update salt hidden fresh) positions =
      referenceOpening heap salt positions := by
  apply reference_opening_salt_congr
  intro index member
  exact Function.update_of_ne (by intro same; subst index; exact unopened member) _ _

/-- The actual eight-block leaf computation, with unused natural indices zeroed. -/
def queryLeaf (message : Message) (salt : Index → Digest) (index : Nat) : OracleComp World Digest :=
  if inside : index < LENGTH then
    hashBlocks ((List.range 8).map fun block => (message ⟨index, inside⟩).extractLsb' (256*block) 256)
      (salt ⟨index, inside⟩)
  else pure 0

def queryLeafExcept (message : Message) (salt : Index → Digest) (hidden : Index)
    (digest : Digest) (index : Nat) : OracleComp World Digest :=
  if index = hidden.val then pure digest else queryLeaf message salt index

def leafValues (compress : Compression) (message : Message) (salt : Index → Digest)
    (index : Nat) : Digest :=
  if inside : index < LENGTH then leafDigest compress (salt ⟨index, inside⟩) (message ⟨index, inside⟩)
  else 0

def leafValuesExcept (compress : Compression) (message : Message) (salt : Index → Digest)
    (hidden : Index) (digest : Digest) (index : Nat) : Digest :=
  if index = hidden.val then digest else leafValues compress message salt index

theorem query_leaf_bound (message : Message) (salt : Index → Digest) (index : Nat) :
    PublicQueryBound (queryLeaf message salt index) 8 := by
  unfold queryLeaf
  split
  · simpa only [List.length_map, List.length_range] using hash_blocks_bound
      ((List.range 8).map fun block => (message ⟨index, by assumption⟩).extractLsb' (256*block) 256)
      (salt ⟨index, by assumption⟩)
  · trivial

theorem query_leaf_except_bound (message : Message) (salt : Index → Digest)
    (hidden : Index) (digest : Digest) (index : Nat) :
    PublicQueryBound (queryLeafExcept message salt hidden digest index) 8 := by
  unfold queryLeafExcept
  split
  · trivial
  · exact query_leaf_bound message salt index

theorem query_leaf_reference (oracle : Oracle) (message : Message) (salt : Index → Digest)
    (index : Nat) : fixedOracleRun oracle (queryLeaf message salt index) =
      pure (leafValues oracle.compression message salt index) := by
  unfold queryLeaf leafValues
  split
  · have result := fixed_hash_blocks oracle
      ((List.range 8).map fun block => (message ⟨index, by assumption⟩).extractLsb' (256*block) 256)
      (salt ⟨index, by assumption⟩) pure
    simpa only [bind_pure, List.foldl_map, fixed_oracle_run_pure, leafDigest] using result
  · exact fixed_oracle_run_pure _ _

theorem query_leaf_except_reference (oracle : Oracle) (message : Message) (salt : Index → Digest)
    (hidden : Index) (digest : Digest) (index : Nat) :
    fixedOracleRun oracle (queryLeafExcept message salt hidden digest index) =
      pure (leafValuesExcept oracle.compression message salt hidden digest index) := by
  unfold queryLeafExcept leafValuesExcept
  split
  · exact fixed_oracle_run_pure _ _
  · exact query_leaf_reference oracle message salt index

def queryTranscriptExcept (message : Message) (salt : Index → Digest) (positions : Positions)
    (hidden : Index) (digest : Digest) : OracleComp World (Commitment × Proof) :=
  queryTranscript (queryHeap LENGTH (queryLeafExcept message salt hidden digest) LOG_LENGTH)
    (Function.update salt hidden 0) positions

attribute [local irreducible] heapQueryBudget queryHeap queryTranscript

theorem query_transcript_except_bound (message : Message) (salt : Index → Digest)
    (positions : Positions) (hidden : Index) (digest : Digest) :
    PublicQueryBound (queryTranscriptExcept message salt positions hidden digest)
      ((1+800*positions.card)*heapQueryBudget 8 LOG_LENGTH) := by
  unfold queryTranscriptExcept
  apply query_transcript_bound
  intro node
  exact query_heap_bound LENGTH _ 8 (query_leaf_except_bound message salt hidden digest) LOG_LENGTH node

theorem query_transcript_except_reference (oracle : Oracle) (message : Message)
    (salt : Index → Digest) (positions : Positions) (hidden : Index) (digest : Digest) :
    fixedOracleRun oracle (queryTranscriptExcept message salt positions hidden digest) =
      let heap := referenceHeap oracle.compression LENGTH
        (leafValuesExcept oracle.compression message salt hidden digest)
      pure (heap 1, referenceOpening heap (Function.update salt hidden 0) positions) := by
  apply query_transcript_reference
  intro node positive inside
  apply query_heap_reference oracle LENGTH _ _
    (query_leaf_except_reference oracle message salt hidden digest) LOG_LENGTH node positive inside
  change LENGTH ≤ LENGTH*node
  have larger := Nat.mul_le_mul_left LENGTH positive
  simpa only [Nat.mul_one] using larger

/-- Restoring the hidden leaf's digest gives precisely the tree for the updated
message and fresh salt; every other leaf is unchanged. -/
theorem leaf_values_except_update (compress : Compression) (message : Message)
    (salt : Index → Digest) (hidden : Index) (value : Entry) (fresh : Digest) :
    leafValuesExcept compress message salt hidden (leafDigest compress fresh value) =
      leafValues compress (Function.update message hidden value) (Function.update salt hidden fresh) := by
  funext index
  unfold leafValuesExcept leafValues
  by_cases same : index = hidden.val
  · subst index
    simp only [dif_pos hidden.isLt, Function.update_self, if_true]
  · rw [if_neg same]
    split
    · rename_i inside
      have different : (⟨index, inside⟩ : Index) ≠ hidden := by
        intro equal
        exact same (congrArg Fin.val equal)
      rw [Function.update_of_ne different, Function.update_of_ne different]
    · rfl

/-- Exact full-transcript continuation after one unopened leaf has been isolated.
The continuation is independent of the fresh salt used in that leaf. -/
theorem query_transcript_hidden_update (oracle : Oracle) (message : Message)
    (salt : Index → Digest) (positions : Positions) (hidden : Index) (unopened : hidden ∉ positions)
    (value : Entry) (fresh : Digest) :
    fixedOracleRun oracle
      (queryTranscriptExcept message salt positions hidden (leafDigest oracle.compression fresh value)) =
      pure (referenceTranscript oracle.compression
        (Function.update message hidden value) (Function.update salt hidden fresh) positions) := by
  rw [query_transcript_except_reference, leaf_values_except_update]
  change pure ((saltedHeap oracle.compression (Function.update message hidden value)
      (Function.update salt hidden fresh)) 1,
    referenceOpening (saltedHeap oracle.compression (Function.update message hidden value)
      (Function.update salt hidden fresh)) (Function.update salt hidden 0) positions) = _
  unfold referenceTranscript
  dsimp only
  rw [reference_opening_hidden_salt _ salt positions hidden unopened 0,
    reference_opening_hidden_salt _ salt positions hidden unopened fresh]
  rfl

end CommitGolfCandidate
