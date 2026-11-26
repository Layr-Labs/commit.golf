import CommitGolfCandidate.PairReplay
import CommitGolfCandidate.PairSound
namespace CommitGolfCandidate.PairCap
open CommitGolf CommitGolf.Riscv OracleComp OracleSpec
set_option maxRecDepth 10000
set_option maxHeartbeats 600000
attribute [local irreducible] readBuffer childrenAt parentAt parents queryChildren replayCapUpper replayChain replayPath recordPath

private def siblings (input : CheckInput) (r : Nat) (c : Children) (upper : Fin 7 → Bool × Digest) (l : Nat) :=
  let i := openingIndex input.positions r
  if l < 16 then lowerSibling input r l else if l = 16 then c.sibling (i.testBit 16) (supplied input (i/131072))
  else if below : l-17<7 then (upper ⟨l-17,below⟩).2 else 0

def extractRecord (input : CheckInput) (r : Nat) : OracleComp World (List (BitVec COMPRESSION_INPUT_LENGTH)) :=
  if input.positions.card ≠ BATCH then replayRecord input r else do
    let c ← queryChildren input (openingIndex input.positions r/131072)
    let tab ← parents input 128
    let upper ← replayCapUpper tab (recordIndex input r)
    let leaf ← replayLeaf (recordIndex input r) (batchSalt input r) (recordValue input r)
    let path ← replayPath leaf.1 (recordPath (recordIndex input r) (siblings input r c upper))
    return leaf.2 ++ path.2

def extractCost (input : CheckInput) := if input.positions.card=BATCH then 5436 else 28

theorem extractRun (o : Oracle) (input : CheckInput) (r : Nat) :
    o.run (extractRecord input r) = pure (authInputs o.compression input r,extractCost input) := by
  by_cases b : input.positions.card=BATCH
  · simp only [extractRecord,if_neg (not_not_intro b),oracle_run_bind,childrenRun,parentsRun,pure_bind,
      replay_cap_upper_run,replay_leaf_run,replay_path_run,oracle_run_pure]
    have eqp : recordPath (recordIndex input r)
        (siblings input r (childrenAt o.compression input (openingIndex input.positions r/131072))
          (fun k => ((recordIndex input r).val.testBit (17+k.val),
            referenceHeap o.compression 128 (capTable o.compression input)
            (((128+(recordIndex input r).val/2^17)/2^k.val) ^^^ 1)))) =
        recordPath (recordIndex input r) (fullSibling o.compression input r) := by
      unfold recordPath recordPathPrefix
      apply List.map_congr_left
      intro l h
      have hl := List.mem_range.mp h
      simp only [siblings,fullSibling,recordIndex,show l-17<7 by omega,↓reduceDIte, show (2:Nat)^17=131072 by decide]
    unfold capTable at eqp
    rw [eqp]
    simp [authInputs,authSalt,authSibling,b,openingInputs,extractCost,record_path_length]
  · rw [extractRecord,if_pos b,replay_record_run]
    simp [authInputs,authSalt,authSibling,b,recordInputs,extractCost,replayRecordCost]

theorem extractBound (input : CheckInput) (r : Nat) :
    IsTotalQueryBound (extractRecord input r) (extractCost input) := by
  by_cases b : input.positions.card=BATCH
  · simp only [extractRecord,extractCost,if_neg (not_not_intro b),if_pos b]
    change IsTotalQueryBound (_ >>= _) (40+(41*128+(120+(4+24))))
    apply isTotalQueryBound_bind (childrenBound input (openingIndex input.positions r/131072))
    intro c; apply isTotalQueryBound_bind (parentsBound input 128)
    intro tab; apply isTotalQueryBound_bind (replay_cap_upper_query_bound tab (recordIndex input r))
    intro upper; apply isTotalQueryBound_bind (replay_leaf_query_bound _ _ _)
    intro leaf
    simp only [bind_pure_comp,IsTotalQueryBound,isQueryBound_map_iff]
    have h := replay_path_query_bound leaf.1 (recordPath (recordIndex input r) (siblings input r c upper))
    rwa [record_path_length] at h
  · rw [extractRecord,if_pos b]
    simpa only [extractCost,replayRecordCost,if_neg b] using replay_record_query_bound input r

end CommitGolfCandidate.PairCap
