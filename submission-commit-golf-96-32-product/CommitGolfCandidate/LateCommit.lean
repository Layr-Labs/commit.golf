import CommitGolfCandidate.LatePasses
import CommitGolfCandidate.LateRoot

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def lastParent (o : Oracle) (m : Message) (ws : List PairCoins) := passes o.compression (leavesDone o m ws) 24
def endState (o : Oracle) (m : Message) (ws : List PairCoins) := haltState (rootCopy (lastParent o m ws))
def endCommit (o : Oracle) (m : Message) (ws : List PairCoins) : Execution :=
  ⟨.success,endState o m ws,911802772,83886079⟩

private theorem begin_parents (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    Entry (leavesDone o m ws) 930 := by
  have a := leaves_done_regs o m ws len
  exact ⟨by simpa only [lt_self_iff_false,if_false] using a.pc,a.selector,a.kind,a.len,a.base,a.root⟩

theorem last_pointers (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    let s := lastParent o m ws
    s.pc=pcAt 3305 ∧ s.getReg .x12=BitVec.ofNat 64 rootSource ∧ s.getReg .x26=BitVec.ofNat 64 rootDestination := by
  let s := leavesDone o m ws
  have done := poses o.compression s (begin_parents o m ws len) 24 (by decide)
  have prev := poses o.compression s (begin_parents o m ws len) 23 (by decide)
  have h : boundary 23=passStart 23 := by decide
  rw [h] at prev
  exact ⟨done.atPC,final_source _ _ prev,done.root⟩

attribute [local irreducible] execute List.range words

private theorem abi_run (m : Message) :
    submission.run .commit m = execute (submission.image .commit) 1099511627776 (startState m) true := by
  have run (c : Submission) : c.run .commit m = execute (c.image .commit) (c.steps .commit) (c.initialState .commit m) true := rfl
  exact (run submission).trans (congrArg (fun n => execute (submission.image .commit) n (startState m) true)
    (show submission.steps .commit=1099511627776 by rfl))
private theorem readRoot (s : MachineState) (cost calls : Nat) :
    (submission.readCommit ⟨.success,s,cost,calls⟩).1 = readBuffer s rootDestination 32 := rfl

attribute [local irreducible] passes leafFold commitImage leavesDone treeM readBuffer rootCopy haltState treeNode initialList

private theorem suffix_run (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) (fuel : Nat) :
    o.run (execute commitImage (total passSteps 24+(11+fuel)) (leavesDone o m ws) true) =
      pure (⟨.success,endState o m ws,169869691,16777215⟩,16777215) := by
  have e := begin_parents o m ws len
  obtain ⟨pc,src,dst⟩ := last_pointers o m ws len
  have cycles : total passCycles 24 = 169869680 := by decide
  have count : total levelSize 24 = 16777215 := by decide
  rw [Nat.add_comm (total passSteps 24),passes_run o _ e 24 (by decide)]
  change (do let (out,n) ← o.run (execute commitImage (11+fuel) (lastParent o m ws) true)
             pure (out.charge (total passCycles 24) (total levelSize 24),total levelSize 24+n)) = _
  rw [Nat.add_comm 11 fuel,commit_exit _ pc src dst,oracle_run_pure,cycles,count,pure_bind]
  rfl

private def spareFuel := 1099511627776-274268571
private theorem fuel_eq : 1099511627776 =
    16842768+(9+(leafSteps 0 LENGTH+(total passSteps 24+(11+spareFuel)))) := by decide

private theorem add_charge (x : ProbComp (Execution × Nat)) (s : MachineState)
    (first second firstCalls secondCalls cost calls : Nat)
    (hcost : first+second=cost) (hcalls : firstCalls+secondCalls=calls)
    (eq : x = pure (⟨.success,s,second,secondCalls⟩,secondCalls)) :
    (do let (out,n) ← x; pure (out.charge first firstCalls,firstCalls+n)) =
      pure (⟨.success,s,cost,calls⟩,calls) := by
  rw [eq,pure_bind]
  simp only [Execution.charge,hcost,hcalls]

private theorem final_continuation (o : Oracle) (m : Message) (ws : List PairCoins) (member : ws ∈ support words) :
    (do let (out,n) ← o.run (execute commitImage (total passSteps 24+(11+spareFuel)) (leavesDone o m ws) true)
        pure (out.charge 741933081 67108864,67108864+n)) = pure (endCommit o m ws,83886079) := by
  unfold endCommit
  exact add_charge _ _ 741933081 169869691 67108864 16777215 911802772 83886079 (by decide) (by decide) (suffix_run o m ws (words_length ws member) spareFuel)

theorem full_commit_run (o : Oracle) (m : Message) :
    o.run (submission.run .commit m) =
      (do let ws ← words; pure (endCommit o m ws,83886079)) := by
  rw [abi_run,commit_image_matches,fuel_eq,run_through_leaves]
  exact bind_congr_of_forall_mem_support words (final_continuation o m)

theorem committed_nodes (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    let s := lastParent o m ws
    let tree := treeM (M := Id) o.compression m (wordTape ws)
    (∀ d ≤ LOG_LENGTH, ∀ i < levelCount d, readBuffer s (nodeAddress d i) 32 = node tree d i) ∧
    (∀ i : Index, readBuffer s (saltAddress i) 24 = wordTape ws i) := by
  dsimp only
  unfold lastParent
  have l := leaves_done_contents o m ws len
  have e := passes_contents _ _ (begin_parents o m ws len) _ _ (initial_nodes o m ws len)
    (leaves_done_gaps o m ws len) l.salts 24 (by decide)
  exact ⟨fun d hd i hi => (e.1 d hd i hi).trans (fixed_tree_node o.compression m (wordTape ws) d i hd hi).symm,e.2.2⟩

theorem committed_root (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    (submission.readCommit (endCommit o m ws)).1 =
      node (treeM (M := Id) o.compression m (wordTape ws)) LOG_LENGTH 0 := by
  obtain ⟨_,src,dst⟩ := last_pointers o m ws len
  rw [endCommit,readRoot,endState,root_copy_contents _ src dst]
  have eq : rootSource=nodeAddress LOG_LENGTH 0 := by decide
  rw [eq]
  exact (committed_nodes o m ws len).1 LOG_LENGTH le_rfl 0 (by decide)

end CommitGolfCandidate.Late
