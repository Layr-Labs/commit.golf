import CommitGolfCandidate.BindingReplay
import CommitGolfCandidate.CapConsistency
import CommitGolfCandidate.S3LeafProbe

/-! Paid replay of the sixteen-level lower records. The parser and machine
bridges remain separate: these records explicitly contain a salt and exactly
sixteen siblings, with every direction fixed by the original ABI index.
Stage 3: the leaf is `s3LeafDigest permutation salt value`, replayed with two
forward permutation calls (`s3HashLeaf`); the sixteen path calls are unchanged. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

structure CapLowerRecord where
  index : Index
  value : Entry
  salt : Digest
  sibling : Fin 16 → Digest

def CapLowerRecord.path (record : CapLowerRecord) : List (Bool × Digest) :=
  List.ofFn fun level : Fin 16 => (record.index.val.testBit level.val, record.sibling level)

theorem cap_lower_path_length (record : CapLowerRecord) : record.path.length = 16 := by
  simp [CapLowerRecord.path]

theorem cap_lower_path_directions (record : CapLowerRecord) :
    record.path.map Prod.fst = (List.range 16).map record.index.val.testBit := by
  rw [CapLowerRecord.path, List.map_ofFn, List.ofFn_eq_map]
  change (List.finRange 16).map (record.index.val.testBit ∘ Fin.val) = _
  rw [← List.map_map, List.map_coe_finRange_eq_range]

def CapLowerRecord.root (record : CapLowerRecord) (compress : Compression)
    (permutation : Perm) : Digest :=
  climb compress (s3LeafDigest permutation record.salt record.value) record.path

/-- Compression inputs of one record: its sixteen path inputs. -/
def CapLowerRecord.inputs (record : CapLowerRecord) (compress : Compression)
    (permutation : Perm) : List (BitVec 512) :=
  openingInputs compress permutation record.salt record.value record.path

theorem cap_lower_inputs_length (record : CapLowerRecord) (compress : Compression)
    (permutation : Perm) : (record.inputs compress permutation).length = 16 := by
  rw [CapLowerRecord.inputs, openingInputs_length, cap_lower_path_length]

/-- Each retained input was queried through World before it is returned. The leaf
is two paid permutation calls; only compression inputs are retained. -/
def capReplayLower (record : CapLowerRecord) : OracleComp World (Digest × List (BitVec 512)) := do
  let leaf ← s3HashLeaf record.salt record.value
  replayPath leaf record.path

theorem cap_replay_lower_run (oracle : Oracle) (record : CapLowerRecord) :
    oracle.run (capReplayLower record) =
      pure ((record.root oracle.compression oracle.permutation,
        record.inputs oracle.compression oracle.permutation), 18) := by
  simp only [capReplayLower, oracle_run_bind, s3_hash_leaf_run, pure_bind, replay_path_run,
    cap_lower_path_length]
  rfl

/-- This bound holds for all replies, including replies inconsistent with a fixed
oracle. A record pays two leaf and sixteen lower calls; the testers' ceiling of
twenty-four per record is kept so every later budget statement is unchanged. -/
theorem cap_replay_lower_query_bound (record : CapLowerRecord) :
    IsTotalQueryBound (capReplayLower record) 24 := by
  unfold capReplayLower
  have exact : IsTotalQueryBound
      (s3HashLeaf record.salt record.value >>= fun leaf => replayPath leaf record.path)
      (2 + 16) := by
    apply isTotalQueryBound_bind (s3_hash_leaf_bound _ _)
    intro leaf
    simpa only [cap_lower_path_length] using replay_path_query_bound leaf record.path
  exact exact.mono (by omega)

/-- Forward duplicate checking occurs after the current record's paid queries,
before any queries for the next record. -/
def capReplayLowerBatch : List CapLowerRecord → CapRootMap →
    OracleComp World (Option (CapRootMap × List (BitVec 512)))
  | [], roots => pure (some (roots, []))
  | record :: rest, roots => do
      let (root, inputs) ← capReplayLower record
      match capInsert roots (capGroup record.index).val root with
      | none => pure none
      | some next =>
          let result ← capReplayLowerBatch rest next
          return result.map fun (finalRoots, laterInputs) => (finalRoots, inputs ++ laterInputs)

def capLowerBatchRoots (compress : Compression) (permutation : Perm) :
    List CapLowerRecord → CapRootMap → Option CapRootMap
  | [], roots => some roots
  | record :: rest, roots => do
      let next ← capInsert roots (capGroup record.index).val (record.root compress permutation)
      capLowerBatchRoots compress permutation rest next

def capLowerBatchInputs (compress : Compression) (permutation : Perm)
    (records : List CapLowerRecord) : List (BitVec 512) :=
  records.flatMap fun record => record.inputs compress permutation

theorem cap_lower_batch_inputs_length (compress : Compression) (permutation : Perm)
    (records : List CapLowerRecord) :
    (capLowerBatchInputs compress permutation records).length = 16 * records.length := by
  induction records with
  | nil => simp [capLowerBatchInputs]
  | cons record rest ih =>
      simp only [capLowerBatchInputs, List.flatMap_cons, List.length_append,
        cap_lower_inputs_length] at ih ⊢
      simp only [List.length_cons]
      omega

theorem cap_replay_lower_batch_query_bound (records : List CapLowerRecord) (roots : CapRootMap) :
    IsTotalQueryBound (capReplayLowerBatch records roots) (24 * records.length) := by
  induction records generalizing roots with
  | nil => trivial
  | cons record rest ih =>
      simp only [capReplayLowerBatch, List.length_cons, Nat.mul_add, Nat.mul_one]
      rw [Nat.add_comm]
      apply isTotalQueryBound_bind (cap_replay_lower_query_bound record)
      rintro ⟨root, inputs⟩
      cases inserted : capInsert roots (capGroup record.index).val root with
      | none => trivial
      | some next =>
          simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using ih next

/-- Successful fixed-oracle evaluation returns the concatenation of precisely the
paid lower-record inputs. No query is omitted by a duplicate-group reuse. -/
theorem cap_replay_lower_batch_run (oracle : Oracle) (records : List CapLowerRecord)
    (roots finalRoots : CapRootMap)
    (accepted : capLowerBatchRoots oracle.compression oracle.permutation records roots =
      some finalRoots) :
    oracle.run (capReplayLowerBatch records roots) =
      pure (some (finalRoots, capLowerBatchInputs oracle.compression oracle.permutation records),
        18 * records.length) := by
  induction records generalizing roots with
  | nil =>
      simp only [capLowerBatchRoots, Option.some.injEq] at accepted
      subst finalRoots
      simp [capReplayLowerBatch, capLowerBatchInputs, oracle_run_pure]
  | cons record rest ih =>
      cases inserted : capInsert roots (capGroup record.index).val
          (record.root oracle.compression oracle.permutation) with
      | none => simp [capLowerBatchRoots, inserted] at accepted
      | some next =>
          have later : capLowerBatchRoots oracle.compression oracle.permutation rest next =
              some finalRoots := by
            simpa [capLowerBatchRoots, inserted] using accepted
          simp only [capReplayLowerBatch]
          erw [oracle_run_bind, cap_replay_lower_run]
          simp only [pure_bind, inserted]
          erw [oracle_run_bind, ih next later]
          simp [oracle_run_pure, capLowerBatchInputs, Nat.mul_add, Nat.add_comm]

/-- An accepted suffix preserves roots that were already known at its entry. -/
theorem cap_lower_batch_preserves (compress : Compression) (permutation : Perm)
    (records : List CapLowerRecord)
    (roots finalRoots : CapRootMap) (group : Nat) (value : Digest)
    (accepted : capLowerBatchRoots compress permutation records roots = some finalRoots)
    (known : roots group = some value) : finalRoots group = some value := by
  induction records generalizing roots with
  | nil =>
      simp only [capLowerBatchRoots, Option.some.injEq] at accepted
      subst finalRoots
      exact known
  | cons record rest ih =>
      cases inserted : capInsert roots (capGroup record.index).val
          (record.root compress permutation) with
      | none => simp [capLowerBatchRoots, inserted] at accepted
      | some next =>
          apply ih next (by simpa [capLowerBatchRoots, inserted] using accepted)
          exact cap_insert_preserves roots next _ group _ value inserted known

/-- Every accepted record, including a duplicate, agrees with the retained group
root. This is the lower-root premise needed by the cap path extractor. -/
theorem cap_lower_batch_member (compress : Compression) (permutation : Perm)
    (records : List CapLowerRecord) (roots finalRoots : CapRootMap)
    (accepted : capLowerBatchRoots compress permutation records roots = some finalRoots)
    (record : CapLowerRecord) (member : record ∈ records) :
    finalRoots (capGroup record.index).val = some (record.root compress permutation) := by
  induction records generalizing roots with
  | nil => simp at member
  | cons head rest ih =>
      cases inserted : capInsert roots (capGroup head.index).val
          (head.root compress permutation) with
      | none => simp [capLowerBatchRoots, inserted] at accepted
      | some next =>
          have later : capLowerBatchRoots compress permutation rest next = some finalRoots := by
            simpa [capLowerBatchRoots, inserted] using accepted
          rcases List.mem_cons.mp member with same | laterMember
          · subst head
            apply cap_lower_batch_preserves compress permutation rest next finalRoots _ _ later
            rw [cap_insert_lookup roots next _ _ _ inserted]
            simp
          · exact ih next later laterMember
end CommitGolfCandidate
