import CommitGolfCandidate.CapLowerReplay
import CommitGolfCandidate.CapBinding
import CommitGolfCandidate.CapPositions
import CommitGolfCandidate.CapKnownView

/-! Complete parsed-batch replay: all lower records are queried and duplicate
checked, then the shared cap is queried with strict suffix/root rejection.
This is the paid semantic bridge; byte parsing and image execution remain
separate obligations before instantiating the machine binding game.
Each record pays two leaf calls, one group call and fourteen truncated
compression calls; the cap pays one truncated compression call per node. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

def capReplayBatch (records : List CapLowerRecord) (proof : List Digest) (root : Digest) :
    OracleComp World (Option (List (BitVec 512))) := do
  let lowerResult ← capReplayLowerBatch records (fun _ => none)
  match lowerResult with
  | none => pure none
  | some (roots, lowerInputs) =>
      let capResult ← capReplayQ (capKnownView roots 8 0) proof
      return capResult.bind fun (reported, rest, capInputs) =>
        if reported = root ∧ rest = [] then some (lowerInputs ++ capInputs) else none

/-- The conservative ceiling counts every lower record, including duplicates,
and every internal cap node on all possible reply continuations. -/
theorem cap_replay_batch_query_bound (records : List CapLowerRecord)
    (proof : List Digest) (root : Digest) :
    IsTotalQueryBound (capReplayBatch records proof root) (24 * records.length + 255) := by
  unfold capReplayBatch
  apply isTotalQueryBound_bind (cap_replay_lower_batch_query_bound records (fun _ => none))
  intro lowerResult
  cases lowerResult with
  | none => trivial
  | some result =>
      rcases result with ⟨roots, lowerInputs⟩
      simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
        cap_replay_height_seven_bound (capKnownView roots 8 0) proof

theorem cap_lower_batch_known (compress : Compression) (permutation : Perm)
    (records : List CapLowerRecord) (roots : CapRootMap)
    (accepted : capLowerBatchRoots compress permutation records (fun _ => none) = some roots)
    (record : CapLowerRecord) (member : record ∈ records) :
    capLeafValue (capKnownView roots 8 0) (capRequestedPath record.index) =
      some (record.root compress permutation) := by
  rw [cap_known_view_leaf, cap_requested_path_index, Nat.zero_add]
  exact cap_lower_batch_member compress permutation records _ roots accepted record member

theorem cap_lower_batch_input_member (compress : Compression) (permutation : Perm)
    (records : List CapLowerRecord)
    (record : CapLowerRecord) (member : record ∈ records)
    (input : BitVec 512) (queried : input ∈ record.inputs compress permutation) :
    input ∈ capLowerBatchInputs compress permutation records := by
  exact List.mem_flatMap.mpr ⟨record, member, queried⟩

/-- Successful decoding pays for the entire accepted lower and cap trace. The
cap trace length itself is the number of cap calls; no free query list is used. -/
theorem cap_replay_batch_run (oracle : Oracle) (records : List CapLowerRecord)
    (proof : List Digest) (root : Digest) (roots : CapRootMap)
    (lowerAccepted : capLowerBatchRoots (s6Compress oracle.compression) oracle.permutation records
      (fun _ => none) = some roots)
    (capAccepted : capDecode (s6Compress oracle.compression) (capKnownView roots 8 0) proof =
      some (root, [])) :
    ∃ capInputs : List (BitVec 512),
      oracle.run (capReplayQ (capKnownView roots 8 0) proof) =
        pure (some (root, [], capInputs), capInputs.length) ∧
      oracle.run (capReplayBatch records proof root) =
        pure (some (capLowerBatchInputs (s6Compress oracle.compression) oracle.permutation records ++
          capInputs), 17 * records.length + capInputs.length) := by
  obtain ⟨capInputs, witness⟩ := cap_decode_witness (s6Compress oracle.compression)
    (capKnownView roots 8 0) proof [] root capAccepted
  have capRun := cap_replay_witness_run oracle witness
  refine ⟨capInputs, capRun, ?_⟩
  simp only [capReplayBatch]
  erw [oracle_run_bind, cap_replay_lower_batch_run oracle records _ roots lowerAccepted]
  simp only [pure_bind]
  erw [oracle_run_bind, capRun]
  simp [oracle_run_pure]

end CommitGolfCandidate
