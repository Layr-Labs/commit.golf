import CommitGolfCandidate.TruncAuthentication
import CommitGolfCandidate.TruncReplay
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv OracleComp OracleSpec
set_option maxRecDepth 9000
set_option maxHeartbeats 200000
attribute [local irreducible] childrenAt parentAt parents queryChildren replayCapUpper replayPath recordPath replayLeaf
attribute [local irreducible] climb pathInputs wideInput recordIndex

private def siblings (i : CheckInput) (r : Nat) (c : Children) (upper : Fin 7 → Bool × Digest) (l : Nat) :=
  let x:=openingIndex i.positions r
  if l<16 then lowerSibling i r l else if l=16 then c.sibling (x.testBit 16) (supplied i (x/131072))
  else if h : l-17<7 then (upper ⟨l-17,h⟩).2 else 0

def selected (i : CheckInput) (r : Nat) (salt : Salt) (sib : Nat→Digest) : OracleComp World (List (BitVec COMPRESSION_INPUT_LENGTH)) := do
  let v ← replayLeaf (recordIndex i r) salt (recordValue i r)
  let p ← replayPath (LENGTH+(recordIndex i r).val) v.1 (recordPath (recordIndex i r) sib)
  return v.2++p.2

theorem selectedRun (o : Oracle) (i : CheckInput) (r : Nat) (s : Salt) (sib : Nat→Digest) :
    o.run (selected i r s sib) =
      pure (openingInputs o.compression (recordIndex i r) s (recordValue i r) (recordPath (recordIndex i r) sib),28) := by
  simp only [selected,oracle_run_bind,replay_leaf_run,pure_bind,replay_path_run,oracle_run_pure,record_path_length,openingInputs] <;> rfl
theorem selectedBound (i : CheckInput) (r : Nat) (s : Salt) (sib : Nat→Digest) : IsTotalQueryBound (selected i r s sib) 28 := by
  unfold selected
  change IsTotalQueryBound (_ >>= _) (4+24)
  apply isTotalQueryBound_bind (replay_leaf_query_bound _ _ _)
  intro v
  simp only [bind_pure_comp,IsTotalQueryBound,isQueryBound_map_iff]
  have h:=replay_path_query_bound (LENGTH+(recordIndex i r).val) v.1 (recordPath (recordIndex i r) sib)
  rwa [record_path_length] at h

def extractRecord (i : CheckInput) (r : Nat) : OracleComp World (List (BitVec COMPRESSION_INPUT_LENGTH)) :=
  if i.positions.card≠BATCH then selected i r (recordSalt i r) (normalSibling i r) else do
    let wide:=wideInput i
    let c ← queryChildren wide (openingIndex i.positions r/131072)
    let tab ← parents wide 128
    let upper ← replayCapUpper tab (recordIndex i r)
    selected i r (batchSalt wide r) (siblings wide r c upper)

def extractCost (i : CheckInput) := if i.positions.card=BATCH then 5436 else 28

theorem extractBound (i : CheckInput) (r : Nat) : IsTotalQueryBound (extractRecord i r) (extractCost i) := by
  by_cases b : i.positions.card=BATCH
  · simp only [extractRecord,extractCost,if_neg (not_not_intro b),if_pos b]
    change IsTotalQueryBound (_ >>= _) (40+(41*128+(120+28)))
    apply isTotalQueryBound_bind (childrenBound (wideInput i) (openingIndex i.positions r/131072));intro c
    apply isTotalQueryBound_bind (parentsBound (wideInput i) 128);intro t
    apply isTotalQueryBound_bind (replay_cap_upper_query_bound t (recordIndex i r));intro upper
    exact selectedBound _ _ _ _
  · simpa only [extractRecord,extractCost,if_pos b,if_neg b] using selectedBound i r (recordSalt i r) (normalSibling i r)

theorem widePositions (i : CheckInput) : (wideInput i).positions=i.positions := by unfold wideInput;split <;> rfl

theorem extractRun (o : Oracle) (i : CheckInput) (r : Nat) :
    o.run (extractRecord i r)=pure (authInputs o.compression i r,extractCost i) := by
  by_cases b : i.positions.card=BATCH
  · simp only [extractRecord,if_neg (not_not_intro b),oracle_run_bind,childrenRun,parentsRun,pure_bind,
      replay_cap_upper_run,selectedRun,authInputs,authSalt,authSibling,if_pos b,extractCost]
    congr 2
    apply congrArg (openingInputs o.compression (recordIndex i r) _ _)
    unfold recordPath recordPathPrefix
    apply List.map_congr_left
    intro l hl
    have below:=List.mem_range.mp hl
    simp only [siblings,fullSibling,widePositions,recordIndex,
      show l-17<7 by omega,↓reduceDIte,show (2:Nat)^17=131072 by decide,capTable] <;> rfl
  · simp only [extractRecord,if_pos b,selectedRun,authInputs,authSalt,authSibling,extractCost,if_neg b]

end CommitGolfCandidate.Trunc
