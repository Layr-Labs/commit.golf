import CommitGolfCandidate.CapTraceBounds
import CommitGolfCandidate.BindingProbe

namespace CommitGolfCandidate
open CommitGolf OracleComp

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
      input ≠ input' ∧ oracle.compression input = oracle.compression input') :
    ∃ replies calls,
      oracle.run (capProbePair leftRecords rightRecords leftProof rightProof root) =
        pure (replies, calls) ∧ ReplyCollision replies := by
  refine ⟨_, _, cap_probe_pair_run oracle _ _ _ _ _ _ _ _ _ leftRun rightRun
    leftBound rightBound, ?_⟩
  apply reply_collision_of_inputs
  obtain ⟨input, leftMember, input', rightMember, different, equal⟩ := collision
  exact ⟨input, List.mem_append_left _ leftMember,
    input', List.mem_append_right _ rightMember, different, equal⟩
end CommitGolfCandidate
