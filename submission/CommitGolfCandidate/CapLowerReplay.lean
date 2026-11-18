import CommitGolfCandidate.BindingReplay
import CommitGolfCandidate.CapConsistency
import CommitGolfCandidate.S3LeafProbe
import CommitGolfCandidate.S6Model

/-! Paid replay of the lower records. A record holds its leaf's salt, the three
other leaf digests of the leaf's group and the fourteen siblings of the group
node, with every direction fixed by the ABI index. Its replay pays two forward
permutation calls for the leaf (`s3HashLeaf`), one for the group window
(`s6HashWindow`) and fourteen compression calls whose replies are truncated to
240 bits (`replayPath`). Every node function takes the node compression; the
tree's is `s6Compress oracle.compression`. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

structure CapLowerRecord where
  index : Index
  value : Entry
  salt : Digest
  others : Fin 3 → Digest
  sibling : Fin 14 → Digest

def CapLowerRecord.path (record : CapLowerRecord) : List (Bool × Digest) :=
  s6RecordPath record.index.val record.sibling

theorem cap_lower_path_length (record : CapLowerRecord) : record.path.length = 14 :=
  s6_record_path_length _ _

theorem cap_lower_path_directions (record : CapLowerRecord) :
    record.path.map Prod.fst = (List.range 14).map (record.index.val/4).testBit :=
  s6_record_path_directions _ _

/-- The group digest of the record's leaf: one permutation call on its group window. -/
def CapLowerRecord.group (record : CapLowerRecord) (permutation : Perm) : Digest :=
  s6RecordGroup permutation record.salt record.value record.index.val record.others

def CapLowerRecord.root (record : CapLowerRecord) (compress : Compression)
    (permutation : Perm) : Digest :=
  climb compress (record.group permutation) record.path

theorem cap_lower_root_eq (record : CapLowerRecord) (compress : Compression) (permutation : Perm) :
    record.root compress permutation =
      s6RecordRoot compress permutation record.salt record.value record.index.val record.others
        record.sibling := rfl

/-- Compression inputs of one record: its fourteen path inputs. -/
def CapLowerRecord.inputs (record : CapLowerRecord) (compress : Compression)
    (permutation : Perm) : List (BitVec 512) :=
  pathInputs compress (record.group permutation) record.path

theorem cap_lower_inputs_length (record : CapLowerRecord) (compress : Compression)
    (permutation : Perm) : (record.inputs compress permutation).length = 14 := by
  rw [CapLowerRecord.inputs, pathInputs_length, cap_lower_path_length]

/-- One forward permutation query; the low 256 bits of the reply. -/
def s6HashWindow (window : BitVec PERMUTATION_WIDTH) : OracleComp World Digest := do
  let reply ← (liftM (World.query (.inr (.inr (.inl window)))) :
    OracleComp World (BitVec PERMUTATION_WIDTH))
  return BitVec.ofNat 256 reply.toNat

theorem s6_hash_window_run (oracle : Oracle) (window : BitVec PERMUTATION_WIDTH) :
    oracle.run (s6HashWindow window) = pure (BitVec.ofNat 256 (oracle.permutation window).toNat, 1) := by
  unfold s6HashWindow
  erw [oracle_run_public_bind oracle (.inr (.inl window))]
  simp only [oracle_run_pure, pure_bind]
  rfl

theorem s6_hash_window_bound (window : BitVec PERMUTATION_WIDTH) :
    IsTotalQueryBound (s6HashWindow window) 1 := by
  unfold s6HashWindow
  erw [isTotalQueryBound_query_bind_iff]
  exact ⟨by simp, fun reply => trivial⟩

/-- Each retained input was queried through World before it is returned. The leaf
is two paid permutation calls and the group one; only compression inputs are retained. -/
def capReplayLower (record : CapLowerRecord) : OracleComp World (Digest × List (BitVec 512)) := do
  let leaf ← s3HashLeaf record.salt record.value
  let group ← s6HashWindow (s6RecordWindow leaf record.index.val record.others)
  replayPath group record.path

theorem cap_replay_lower_run (oracle : Oracle) (record : CapLowerRecord) :
    oracle.run (capReplayLower record) =
      pure ((record.root (s6Compress oracle.compression) oracle.permutation,
        record.inputs (s6Compress oracle.compression) oracle.permutation), 17) := by
  simp only [capReplayLower, oracle_run_bind, s3_hash_leaf_run, s6_hash_window_run, pure_bind,
    replay_path_run, cap_lower_path_length]
  rfl

/-- This bound holds for all replies, including replies inconsistent with a fixed
oracle. A record pays two leaf calls, one group call and fourteen lower calls; the
ceiling of twenty-four per record is kept so every later budget statement is unchanged. -/
theorem cap_replay_lower_query_bound (record : CapLowerRecord) :
    IsTotalQueryBound (capReplayLower record) 24 := by
  unfold capReplayLower
  have exact : IsTotalQueryBound
      (s3HashLeaf record.salt record.value >>= fun leaf =>
        s6HashWindow (s6RecordWindow leaf record.index.val record.others) >>= fun group =>
          replayPath group record.path)
      (2 + (1 + 14)) := by
    apply isTotalQueryBound_bind (s3_hash_leaf_bound _ _)
    intro leaf
    apply isTotalQueryBound_bind (s6_hash_window_bound _)
    intro group
    simpa only [cap_lower_path_length] using replay_path_query_bound group record.path
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
    (capLowerBatchInputs compress permutation records).length = 14 * records.length := by
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
    (accepted : capLowerBatchRoots (s6Compress oracle.compression) oracle.permutation records roots =
      some finalRoots) :
    oracle.run (capReplayLowerBatch records roots) =
      pure (some (finalRoots,
        capLowerBatchInputs (s6Compress oracle.compression) oracle.permutation records),
        17 * records.length) := by
  induction records generalizing roots with
  | nil =>
      simp only [capLowerBatchRoots, Option.some.injEq] at accepted
      subst finalRoots
      simp [capReplayLowerBatch, capLowerBatchInputs, oracle_run_pure]
  | cons record rest ih =>
      cases inserted : capInsert roots (capGroup record.index).val
          (record.root (s6Compress oracle.compression) oracle.permutation) with
      | none => simp [capLowerBatchRoots, inserted] at accepted
      | some next =>
          have later : capLowerBatchRoots (s6Compress oracle.compression) oracle.permutation rest next =
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
