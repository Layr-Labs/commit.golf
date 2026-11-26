import CommitGolfCandidate.S5Exit
import CommitGolfCandidate.S5AllPasses
import CommitGolfCandidate.S5ChainPass
namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Chained
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late (PairCoins)
set_option maxRecDepth 20000
attribute [local irreducible] execute readBuffer leavesDone List.range

theorem all_stages (h : Height) : StageLaw h := by
  by_cases ch : chained h
  · exact chain_pass h ch
  · exact plain_pass h ch

noncomputable def beforeExit (o : Oracle) (m : Message) (ws : List PairCoins) : MachineState :=
  if len : ws.length=pairCount then (through_root all_stages o m ws len).choose else leavesDone o m ws

theorem before_spec (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    let t := beforeExit o m ws
    t.pc=pcAt 18478 ∧ Common t ∧
      TreeState o.compression (fun k=>(initialList o.compression m (wordTape ws))[k]?.getD 0) (wordTape ws) 24 t ∧
      Runs .commit true o (leavesDone o m ws) t 40999733 120231543 11318830 := by
  unfold beforeExit
  rw [dif_pos len]
  exact (through_root all_stages o m ws len).choose_spec

noncomputable def endCommit (o : Oracle) (m : Message) (ws : List PairCoins) : Execution :=
  ⟨.success,exited (beforeExit o m ws),860276380,78427694⟩

private theorem suffix (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) (fuel : Nat) :
    o.run (execute commitImage ((fuel+14)+40999733) (leavesDone o m ws) true) =
      pure (⟨.success,exited (beforeExit o m ws),120231557,11318830⟩,11318830) := by
  obtain ⟨pc,cm,_,parents⟩:=before_spec o m ws len
  rw [parents]
  change (do let (out,k) ← o.run (execute commitImage (fuel+14) (beforeExit o m ws) true)
             pure (out.charge 120231543 11318830,11318830+k)) = _
  rw [root_exit _ pc cm,oracle_run_pure,pure_bind]
  rfl

private theorem commit_abi (s : Submission) (m : Message) :
    s.run .commit m = execute (s.image .commit) (s.steps .commit) (s.initialState .commit m) true := rfl

private theorem image_run (m : Message) :
    Artifact.submission.run .commit m = execute commitImage 68719476736 (start m) true :=
  (commit_abi Artifact.submission m).trans (congrArg (fun n => execute commitImage n (start m) true)
    (show Artifact.submission.steps .commit=68719476736 by rfl))

private theorem add_charge (x : ProbComp (Execution × Nat)) (s : MachineState)
    (first second firstCalls secondCalls cost calls : Nat)
    (hcost : first+second=cost) (hcalls : firstCalls+secondCalls=calls)
    (eq : x = pure (⟨.success,s,second,secondCalls⟩,secondCalls)) :
    (do let (out,n) ← x; pure (out.charge first firstCalls,firstCalls+n)) =
      pure (⟨.success,s,cost,calls⟩,calls) := by
  rw [eq,pure_bind]
  simp only [Execution.charge,hcost,hcalls]

private def suffixFuel := (68458525862+14)+40999733
private theorem after_coins (o : Oracle) (m : Message) (ws : List PairCoins) (hw : ws ∈ support coinTape) :
    (do let (out,n) ← o.run (execute commitImage suffixFuel (leavesDone o m ws) true)
        pure (out.charge 740044823 67108864,67108864+n)) = pure (endCommit o m ws,78427694) :=
  add_charge _ _ 740044823 120231557 67108864 11318830 860276380 78427694 (by decide) (by decide) (suffix o m ws (words_length ws hw) 68458525862)

theorem full_commit_run (o : Oracle) (m : Message) :
    o.run (Artifact.submission.run .commit m) =
      (do let ws ← coinTape; pure (endCommit o m ws,78427694)) :=
  (congrArg o.run (image_run m)).trans <| (run_through_leaves o m suffixFuel).trans <|
    bind_congr_of_forall_mem_support coinTape (after_coins o m)

theorem committed_root (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    (Artifact.submission.readCommit (endCommit o m ws)).1 =
      Late.node (S5Hiding.tree o.compression m (wordTape ws)) LOG_LENGTH 0 := by
  obtain ⟨_,cm,tree,_⟩:=before_spec o m ws len
  change readBuffer (exited _) rootDestination 32=_
  rw [exited_root _ cm,show rootSource=nodeAddress LOG_LENGTH 0 by decide]
  apply (tree.nodes LOG_LENGTH (by decide) 0 (by decide)).trans
  exact (fixed_tree_node _ _ _ _ _ le_rfl (by decide)).symm
end CommitGolfCandidate.S5Machine
