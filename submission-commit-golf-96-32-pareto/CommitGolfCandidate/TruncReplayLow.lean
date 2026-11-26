import CommitGolfCandidate.TruncReplayPath
import CommitGolfCandidate.BindingReplay
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv OracleComp OracleSpec
set_option maxRecDepth 10000
set_option maxHeartbeats 55000
attribute [local irreducible] lowerHash climb storeNode pathInputs

/-- For the reduction only, replay both child records even when one is absent.
This fixes the reconstruction cost at forty queries per cap pair. -/
def queryLow (input : CheckInput) (r : Nat) : OracleComp World Digest := do
  let leaf ← replayLeaf (recordIndex input r) (batchSalt input r) (recordValue input r)
  let node ← replayPath (LENGTH+(recordIndex input r).val) leaf.1 (recordPathPrefix 16 (recordIndex input r) (lowerSibling input r))
  return node.1

theorem lowRun (o : Oracle) (input : CheckInput) (r : Nat) :
    o.run (queryLow input r) = pure (lowerHash o.compression input r,20) := by
  simp only [queryLow,oracle_run_bind,replay_leaf_run,pure_bind,replay_path_run,oracle_run_pure]
  simp only [lowerHash,recordAncestor,record_path_prefix_length,Nat.reduceAdd,Nat.add_zero]

theorem lowBound (input : CheckInput) (r : Nat) : IsTotalQueryBound (queryLow input r) 20 := by
  unfold queryLow
  change IsTotalQueryBound (_ >>= _) (4+16)
  apply isTotalQueryBound_bind (replay_leaf_query_bound _ _ _)
  intro leaf
  simp only [bind_pure_comp,IsTotalQueryBound,isQueryBound_map_iff]
  exact replay_path_query_bound _ _ _

end CommitGolfCandidate.Trunc
