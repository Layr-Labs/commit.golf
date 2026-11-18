import CommitGolfCandidate.CapTraceBounds
import CommitGolfCandidate.BindingProbe
import CommitGolfCandidate.S6GroupBinding
import CommitGolfCandidate.CapRecordBinding

/-! Collision extraction for two accepted cap batches, and charged reply probes.
Two accepted records at one index with different values give one of three
events: two replayed leaves with one digest, two replayed group words with one
group digest, or two replayed compression inputs whose replies agree on their
low 240 bits. The replay first pays for the checker queries; only then does the
probe reread recorded inputs. A syntactic take bounds all reply continuations,
including unsuccessful decodes. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp

/-- A width-explicit projection of the same public compression table. -/
def capCompression (oracle : Oracle) : BitVec 512 → Digest := oracle.compression

private theorem cap_probe_inputs_run (oracle : Oracle) (inputs : List (BitVec 512)) :
    oracle.run (probeInputs inputs) =
      pure (inputs.map (fun input => (input, capCompression oracle input)), inputs.length) :=
  probe_inputs_run oracle inputs

def capProbeBatch (records : List CapLowerRecord) (proof : List Digest) (root : Digest) :
    OracleComp World CompressionReplies := do
  let result ← capReplayBatch records proof root
  probeInputs ((result.getD []).take (24 * records.length + 255))

theorem cap_probe_batch_query_bound (records : List CapLowerRecord)
    (proof : List Digest) (root : Digest) :
    IsTotalQueryBound (capProbeBatch records proof root)
      (2 * (24 * records.length + 255)) := by
  unfold capProbeBatch
  rw [two_mul]
  apply isTotalQueryBound_bind (cap_replay_batch_query_bound records proof root)
  intro result
  exact (probe_inputs_bound ((result.getD []).take (24 * records.length + 255))).mono
    (List.length_take_le _ _)

/-- On an accepted fixed-oracle trace the guard discards no recorded input. -/
theorem cap_probe_batch_run (oracle : Oracle) (records : List CapLowerRecord)
    (proof : List Digest) (root : Digest) (inputs : List (BitVec 512)) (calls : Nat)
    (run : oracle.run (capReplayBatch records proof root) = pure (some inputs, calls))
    (bounded : inputs.length ≤ 24 * records.length + 255) :
    oracle.run (capProbeBatch records proof root) =
      pure (inputs.map (fun input => (input, capCompression oracle input)),
        calls + inputs.length) := by
  unfold capProbeBatch
  rw [oracle_run_bind, run]
  simp only [pure_bind, Option.getD_some, List.take_of_length_le bounded]
  rw [cap_probe_inputs_run]
  erw [pure_bind]

def capProbePair (leftRecords rightRecords : List CapLowerRecord)
    (leftProof rightProof : List Digest) (root : Digest) :
    OracleComp World CompressionReplies := do
  let left ← capProbeBatch leftRecords leftProof root
  let right ← capProbeBatch rightRecords rightProof root
  return left ++ right

theorem cap_probe_pair_query_bound (leftRecords rightRecords : List CapLowerRecord)
    (leftProof rightProof : List Digest) (root : Digest) :
    IsTotalQueryBound (capProbePair leftRecords rightRecords leftProof rightProof root)
      (2 * (24 * leftRecords.length + 255) +
        2 * (24 * rightRecords.length + 255)) := by
  unfold capProbePair
  apply isTotalQueryBound_bind
    (cap_probe_batch_query_bound leftRecords leftProof root)
  intro left
  simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
    cap_probe_batch_query_bound rightRecords rightProof root

/-- At most LENGTH records in each claim fit the conservative detector ceiling.
The adversary's own queries are accounted for separately by the later wrapper. -/
theorem cap_probe_pair_ceiling (leftRecords rightRecords : List CapLowerRecord)
    (leftProof rightProof : List Digest) (root : Digest)
    (leftBound : leftRecords.length ≤ LENGTH) (rightBound : rightRecords.length ≤ LENGTH) :
    IsTotalQueryBound (capProbePair leftRecords rightRecords leftProof rightProof root)
      (2 * capReplayCeiling) := by
  apply (cap_probe_pair_query_bound leftRecords rightRecords leftProof rightProof root).mono
  unfold capReplayCeiling
  omega

theorem cap_probe_pair_run (oracle : Oracle)
    (leftRecords rightRecords : List CapLowerRecord)
    (leftProof rightProof : List Digest) (root : Digest)
    (leftInputs rightInputs : List (BitVec 512)) (leftCalls rightCalls : Nat)
    (leftRun : oracle.run (capReplayBatch leftRecords leftProof root) =
      pure (some leftInputs, leftCalls))
    (rightRun : oracle.run (capReplayBatch rightRecords rightProof root) =
      pure (some rightInputs, rightCalls))
    (leftBound : leftInputs.length ≤ 24 * leftRecords.length + 255)
    (rightBound : rightInputs.length ≤ 24 * rightRecords.length + 255) :
    oracle.run (capProbePair leftRecords rightRecords leftProof rightProof root) =
      pure ((leftInputs ++ rightInputs).map (fun input => (input, capCompression oracle input)),
        (leftCalls + leftInputs.length) + (rightCalls + rightInputs.length)) := by
  unfold capProbePair
  rw [oracle_run_bind, cap_probe_batch_run oracle _ _ _ _ _ leftRun leftBound]
  simp only [pure_bind]
  rw [oracle_run_bind, cap_probe_batch_run oracle _ _ _ _ _ rightRun rightBound]
  simp only [pure_bind, oracle_run_pure, Nat.add_zero, List.map_append]

/-- The accepted-trace collision becomes a winning event expressed solely in
returned public replies: two different inputs whose replies agree on their low
240 bits. No hidden compression table occurs in `TruncReplyCollision`. -/
theorem cap_probe_pair_collision (oracle : Oracle)
    (leftRecords rightRecords : List CapLowerRecord)
    (leftProof rightProof : List Digest) (root : Digest)
    (leftInputs rightInputs : List (BitVec 512)) (leftCalls rightCalls : Nat)
    (leftRun : oracle.run (capReplayBatch leftRecords leftProof root) =
      pure (some leftInputs, leftCalls))
    (rightRun : oracle.run (capReplayBatch rightRecords rightProof root) =
      pure (some rightInputs, rightCalls))
    (leftBound : leftInputs.length ≤ 24 * leftRecords.length + 255)
    (rightBound : rightInputs.length ≤ 24 * rightRecords.length + 255)
    (collision : ∃ input ∈ leftInputs, ∃ input' ∈ rightInputs,
      input ≠ input' ∧ s6Compress oracle.compression input = s6Compress oracle.compression input') :
    ∃ replies calls,
      oracle.run (capProbePair leftRecords rightRecords leftProof rightProof root) =
        pure (replies, calls) ∧ TruncReplyCollision replies := by
  refine ⟨_, _, cap_probe_pair_run oracle _ _ _ _ _ _ _ _ _ leftRun rightRun
    leftBound rightBound, ?_⟩
  obtain ⟨input, leftMember, input', rightMember, different, equal⟩ := collision
  exact ⟨(input, capCompression oracle input),
    List.mem_map_of_mem (List.mem_append_left _ leftMember),
    (input', capCompression oracle input'),
    List.mem_map_of_mem (List.mem_append_right _ rightMember), different, equal⟩

/-! ### Replayed leaves and group words -/

/-- The (salt, value) leaves a batch replays, in record order. -/
def capRecordLeaves (records : List CapLowerRecord) : List (Digest × Entry) :=
  records.map fun record => (record.salt, record.value)

theorem cap_record_leaves_length (records : List CapLowerRecord) :
    (capRecordLeaves records).length = records.length := by
  simp [capRecordLeaves]

/-- The leaf replies a fixed oracle gives to `probeLeaves`. -/
def s3LeafReplies (permutation : Perm) (items : List (Digest × Entry)) : LeafReplies :=
  items.map fun item => (item, s3LeafDigest permutation item.1 item.2)

/-- The 1024-bit word of a group call: the four leaf digests in slot order. -/
def s6GroupWord (d0 d1 d2 d3 : Digest) : BitVec 1024 :=
  BitVec.ofNat 1024 (d0.toNat + d1.toNat * 2 ^ 256 + d2.toNat * 2 ^ 512 + d3.toNat * 2 ^ 768)

theorem s6_group_word_enc (d0 d1 d2 d3 : Digest) :
    Permutation.s6SingleCall.enc (s6GroupWord d0 d1 d2 d3) = s6GroupInput d0 d1 d2 d3 := by
  have b0 := d0.isLt
  have b1 := d1.isLt
  have b2 := d2.isLt
  have b3 := d3.isLt
  have bound : d0.toNat + d1.toNat * 2 ^ 256 + d2.toNat * 2 ^ 512 + d3.toNat * 2 ^ 768 <
      2 ^ 1024 := by omega
  simp only [Permutation.s6SingleCall, s6GroupWord, s6GroupInput, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bound]
  rfl

theorem s6_group_word_injective {d0 d1 d2 d3 e0 e1 e2 e3 : Digest}
    (equal : s6GroupWord d0 d1 d2 d3 = s6GroupWord e0 e1 e2 e3) :
    d0 = e0 ∧ d1 = e1 ∧ d2 = e2 ∧ d3 = e3 := by
  have b0 := d0.isLt
  have b1 := d1.isLt
  have b2 := d2.isLt
  have b3 := d3.isLt
  have c0 := e0.isLt
  have c1 := e1.isLt
  have c2 := e2.isLt
  have c3 := e3.isLt
  have numbers := congrArg BitVec.toNat equal
  simp only [s6GroupWord, BitVec.toNat_ofNat] at numbers
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at numbers
  refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_,
    BitVec.eq_of_toNat_eq ?_⟩ <;> omega

/-- The group word of a record's window: the own digest at place `index % 4`,
the three supplied digests at the other places. -/
def s6RecordWord (own : Digest) (index : Nat) (others : Fin 3 → Digest) : BitVec 1024 :=
  if index % 4 = 0 then s6GroupWord own (others 0) (others 1) (others 2)
  else if index % 4 = 1 then s6GroupWord (others 0) own (others 1) (others 2)
  else if index % 4 = 2 then s6GroupWord (others 0) (others 1) own (others 2)
  else s6GroupWord (others 0) (others 1) (others 2) own

theorem s6_record_word_enc (own : Digest) (index : Nat) (others : Fin 3 → Digest) :
    Permutation.s6SingleCall.enc (s6RecordWord own index others) =
      s6RecordWindow own index others := by
  unfold s6RecordWord s6RecordWindow
  split_ifs <;> exact s6_group_word_enc _ _ _ _

theorem s6_record_word_own {own own' : Digest} {index : Nat} {others others' : Fin 3 → Digest}
    (equal : s6RecordWord own index others = s6RecordWord own' index others') : own = own' := by
  unfold s6RecordWord at equal
  split_ifs at equal
  · exact (s6_group_word_injective equal).1
  · exact (s6_group_word_injective equal).2.1
  · exact (s6_group_word_injective equal).2.2.1
  · exact (s6_group_word_injective equal).2.2.2

/-- The group word of a record for a given own leaf digest. -/
def capRecordWord (record : CapLowerRecord) (leaf : Digest) : BitVec 1024 :=
  s6RecordWord leaf record.index.val record.others

/-- A record's group digest is one permutation call on its group word. -/
theorem cap_record_group_word (record : CapLowerRecord) (permutation : Perm) :
    record.group permutation = BitVec.ofNat 256 (permutation (Permutation.s6SingleCall.enc
      (capRecordWord record (s3LeafDigest permutation record.salt record.value)))).toNat := by
  rw [capRecordWord, s6_record_word_enc]
  rfl

/-- Two records at one index with the same group word have the same own leaf digest. -/
theorem cap_record_word_own (left right : CapLowerRecord) (sameIndex : left.index = right.index)
    (leaf leaf' : Digest) (equal : capRecordWord left leaf = capRecordWord right leaf') :
    leaf = leaf' := by
  unfold capRecordWord at equal
  rw [sameIndex] at equal
  exact s6_record_word_own equal

/-- The group words of a batch under a fixed permutation, in record order. -/
def capRecordWords (permutation : Perm) (records : List CapLowerRecord) : List (BitVec 1024) :=
  records.map fun record => capRecordWord record (s3LeafDigest permutation record.salt record.value)

theorem cap_record_words_length (permutation : Perm) (records : List CapLowerRecord) :
    (capRecordWords permutation records).length = records.length := by
  simp [capRecordWords]

/-- The group replies a fixed oracle gives to `probeGroups`. -/
def s6GroupReplies (permutation : Perm) (words : List (BitVec 1024)) :
    List (BitVec 1024 × Digest) :=
  words.map fun word =>
    (word, BitVec.ofNat 256 (permutation (Permutation.s6SingleCall.enc word)).toNat)

/-- Replay the leaves of the records (two paid permutation calls each) and list
their group words. -/
def capGroupWords : List CapLowerRecord → OracleComp World (List (BitVec 1024))
  | [] => pure []
  | record :: rest => do
      let leaf ← s3HashLeaf record.salt record.value
      let words ← capGroupWords rest
      return capRecordWord record leaf :: words

theorem cap_group_words_run (oracle : Oracle) (records : List CapLowerRecord) :
    oracle.run (capGroupWords records) =
      pure (capRecordWords oracle.permutation records, 2 * records.length) := by
  induction records with
  | nil => exact oracle_run_pure _ _
  | cons record rest ih =>
    simp only [capGroupWords]
    rw [oracle_run_bind, s3_hash_leaf_run]
    simp only [pure_bind]
    rw [oracle_run_bind, ih]
    simp only [pure_bind, oracle_run_pure, List.length_cons, capRecordWords, List.map_cons]
    congr 2
    omega

theorem cap_group_words_bound (records : List CapLowerRecord) :
    IsTotalQueryBound (capGroupWords records) (2 * records.length) := by
  induction records with
  | nil => trivial
  | cons record rest ih =>
    simp only [capGroupWords]
    have total : 2 * (record :: rest).length = 2 + (2 * rest.length + 0) := by
      simp only [List.length_cons]; omega
    rw [total]
    apply isTotalQueryBound_bind (s3_hash_leaf_bound _ _)
    intro leaf
    apply isTotalQueryBound_bind ih
    intro words
    trivial

/-! ### Accepted batches: extraction for a fixed oracle -/

theorem oracle_run_pure_unique (oracle : Oracle) {α : Type} (computation : OracleComp World α)
    (first second : α × Nat) (firstRun : oracle.run computation = pure first)
    (secondRun : oracle.run computation = pure second) : first = second := by
  have reachable : first ∈ support (oracle.run computation) := by
    rw [firstRun]
    simp
  rw [secondRun] at reachable
  exact eq_of_mem_support_pure second reachable

/-- An accepted batch has the paid replay trace of its lower records followed
by the given cap trace. -/
theorem cap_batch_run_of_cap (oracle : Oracle) (records : List CapLowerRecord)
    (proof : List Digest) (root : Digest) (roots : CapRootMap)
    (lower : capLowerBatchRoots (s6Compress oracle.compression) oracle.permutation records
      (fun _ => none) = some roots)
    (cap : capDecode (s6Compress oracle.compression) (capKnownView roots 8 0) proof =
      some (root, []))
    (capInputs : List (BitVec 512))
    (capRun : oracle.run (capReplayQ (capKnownView roots 8 0) proof) =
      pure (some (root, [], capInputs), capInputs.length)) :
    oracle.run (capReplayBatch records proof root) =
      pure (some (capLowerBatchInputs (s6Compress oracle.compression) oracle.permutation records ++
        capInputs), 17 * records.length + capInputs.length) := by
  obtain ⟨capInputs', capRun', batchRun⟩ :=
    cap_replay_batch_run oracle records proof root roots lower cap
  have same := oracle_run_pure_unique oracle _ _ _ capRun capRun'
  simp only [Prod.mk.injEq, Option.some.injEq] at same
  rw [same.1.2.2]
  exact batchRun

/-- Any conflicting original values at one index yield a leaf-reply collision
among the replayed leaves of the two batches, a group-reply collision among
their group words, or two different inputs in the full paid accepted traces
(lower paths and caps) whose replies agree on their low 240 bits. -/
theorem cap_batch_collision (oracle : Oracle)
    (leftRecords rightRecords : List CapLowerRecord)
    (leftProof rightProof : List Digest) (root : Digest)
    (leftRoots rightRoots : CapRootMap)
    (leftLower : capLowerBatchRoots (s6Compress oracle.compression) oracle.permutation leftRecords
      (fun _ => none) = some leftRoots)
    (rightLower : capLowerBatchRoots (s6Compress oracle.compression) oracle.permutation rightRecords
      (fun _ => none) = some rightRoots)
    (leftCap : capDecode (s6Compress oracle.compression) (capKnownView leftRoots 8 0) leftProof =
      some (root, []))
    (rightCap : capDecode (s6Compress oracle.compression) (capKnownView rightRoots 8 0) rightProof =
      some (root, []))
    (leftRecord rightRecord : CapLowerRecord)
    (leftMember : leftRecord ∈ leftRecords) (rightMember : rightRecord ∈ rightRecords)
    (sameIndex : leftRecord.index = rightRecord.index)
    (different : leftRecord.value ≠ rightRecord.value) :
    ∃ leftCapInputs rightCapInputs : List (BitVec 512),
      oracle.run (capReplayBatch leftRecords leftProof root) =
        pure (some (capLowerBatchInputs (s6Compress oracle.compression) oracle.permutation leftRecords ++
          leftCapInputs), 17 * leftRecords.length + leftCapInputs.length) ∧
      oracle.run (capReplayBatch rightRecords rightProof root) =
        pure (some (capLowerBatchInputs (s6Compress oracle.compression) oracle.permutation rightRecords ++
          rightCapInputs), 17 * rightRecords.length + rightCapInputs.length) ∧
      (LeafCollision (s3LeafReplies oracle.permutation
          (capRecordLeaves leftRecords ++ capRecordLeaves rightRecords)) ∨
        GroupCollision (s6GroupReplies oracle.permutation
          (capRecordWords oracle.permutation (leftRecords ++ rightRecords))) ∨
        ∃ input ∈ capLowerBatchInputs (s6Compress oracle.compression) oracle.permutation leftRecords ++
            leftCapInputs,
          ∃ input' ∈ capLowerBatchInputs (s6Compress oracle.compression) oracle.permutation rightRecords ++
              rightCapInputs,
            input ≠ input' ∧
              s6Compress oracle.compression input = s6Compress oracle.compression input') := by
  have directions : leftRecord.path.map Prod.fst = rightRecord.path.map Prod.fst := by
    rw [cap_lower_path_directions, cap_lower_path_directions, sameIndex]
  have rightKnown : capLeafValue (capKnownView rightRoots 8 0)
      (capRequestedPath leftRecord.index) =
        some (climb (s6Compress oracle.compression) (rightRecord.group oracle.permutation)
          rightRecord.path) := by
    rw [sameIndex]
    exact cap_lower_batch_known _ _ _ _ rightLower _ rightMember
  obtain ⟨leftCapInputs, rightCapInputs, leftCapRun, rightCapRun, outcome⟩ :=
    cap_record_collision oracle leftRecord.index
      (capKnownView leftRoots 8 0) (capKnownView rightRoots 8 0)
      leftProof rightProof [] [] root (leftRecord.group oracle.permutation)
      (rightRecord.group oracle.permutation) leftRecord.path rightRecord.path directions
      leftCap rightCap (cap_lower_batch_known _ _ _ _ leftLower _ leftMember) rightKnown
  refine ⟨leftCapInputs, rightCapInputs,
    cap_batch_run_of_cap oracle leftRecords leftProof root leftRoots leftLower leftCap _ leftCapRun,
    cap_batch_run_of_cap oracle rightRecords rightProof root rightRoots rightLower rightCap _
      rightCapRun, ?_⟩
  rcases outcome with groups | ⟨input, inputMember, input', inputMember', collision⟩
  · rw [cap_record_group_word, cap_record_group_word] at groups
    by_cases words : capRecordWord leftRecord
        (s3LeafDigest oracle.permutation leftRecord.salt leftRecord.value) =
      capRecordWord rightRecord
        (s3LeafDigest oracle.permutation rightRecord.salt rightRecord.value)
    · have leaves := cap_record_word_own leftRecord rightRecord sameIndex _ _ words
      refine Or.inl ⟨((leftRecord.salt, leftRecord.value), _), ?_,
        ((rightRecord.salt, rightRecord.value), _), ?_, different, leaves⟩
      · exact List.mem_map_of_mem (List.mem_append_left _
          (List.mem_map_of_mem (f := fun record : CapLowerRecord => (record.salt, record.value))
            leftMember))
      · exact List.mem_map_of_mem (List.mem_append_right _
          (List.mem_map_of_mem (f := fun record : CapLowerRecord => (record.salt, record.value))
            rightMember))
    · refine Or.inr (Or.inl ⟨(_, _), ?_, (_, _), ?_, words, groups⟩)
      · exact List.mem_map_of_mem (List.mem_map_of_mem (List.mem_append_left _ leftMember))
      · exact List.mem_map_of_mem (List.mem_map_of_mem (List.mem_append_right _ rightMember))
  · refine Or.inr (Or.inr ⟨input, ?_, input', ?_, collision⟩)
    · rcases List.mem_append.mp inputMember with lower | cap
      · exact List.mem_append_left _ (cap_lower_batch_input_member _ _ _ _ leftMember _ lower)
      · exact List.mem_append_right _ cap
    · rcases List.mem_append.mp inputMember' with lower | cap
      · exact List.mem_append_left _ (cap_lower_batch_input_member _ _ _ _ rightMember _ lower)
      · exact List.mem_append_right _ cap
end CommitGolfCandidate
