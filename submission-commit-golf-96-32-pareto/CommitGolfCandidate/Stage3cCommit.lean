import CommitGolfCandidate.Stage3cTowerExit
import CommitGolfCandidate.Stage3cTreeStart
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late (PairCoins)
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] execute readBuffer leavesDone List.range

private def through_root (o : Oracle) (m : Message) (ws : List PairCoins) (len:ws.length=pairCount) :=
  let a:=leaves_done_regs o m ws len
  parent_tower o (leavesDone o m ws) _ _ (by simpa only [if_neg (Nat.lt_irrefl LENGTH)] using a.pc)
    ⟨a.mode,a.len,a.kind,a.td,a.root,a.scratch,a.strideMsg,a.strideRow,a.spare⟩ (initial_tree o m ws len)
noncomputable def beforeExit (o : Oracle) (m : Message) (ws : List PairCoins) : MachineState :=
  if len : ws.length=pairCount then (through_root o m ws len).choose else leavesDone o m ws

theorem before_spec (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    let t := beforeExit o m ws
    t.pc=pcAt 11529 ∧ Common t ∧
      TreeState o.compression (fun k=>(initialList o.compression m (wordTape ws))[k]?.getD 0) (wordTape ws) 24 t ∧
      Runs .commit true o (leavesDone o m ws) t 60041451 178888676 16978175 := by
  unfold beforeExit
  rw [dif_pos len]
  exact (through_root o m ws len).choose_spec

noncomputable def endCommit (o : Oracle) (m : Message) (ws : List PairCoins) : Execution :=
  ⟨.success,exited (beforeExit o m ws),911200264,84087039⟩

private theorem suffix (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) (fuel : Nat) :
    o.run (execute commitImage ((fuel+14)+60041451) (leavesDone o m ws) true) =
      pure (⟨.success,exited (beforeExit o m ws),178888690,16978175⟩,16978175) := by
  obtain ⟨pc,cm,_,parents⟩:=before_spec o m ws len
  rw [parents]
  change (do let (out,k) ← o.run (execute commitImage (fuel+14) (beforeExit o m ws) true)
             pure (out.charge 178888676 16978175,16978175+k)) = _
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

private def suffixFuel := (68438828785+14)+60041451
private theorem after_coins (o : Oracle) (m : Message) (ws : List PairCoins) (hw : ws ∈ support coinTape) :
    (do let (out,n) ← o.run (execute commitImage suffixFuel (leavesDone o m ws) true)
        pure (out.charge 732311574 67108864,67108864+n)) = pure (endCommit o m ws,84087039) :=
  add_charge _ _ 732311574 178888690 67108864 16978175 911200264 84087039 (by decide) (by decide) (suffix o m ws (words_length ws hw) 68438828785)

theorem full_commit_run (o : Oracle) (m : Message) :
    o.run (Artifact.submission.run .commit m) =
      (do let ws ← coinTape; pure (endCommit o m ws,84087039)) :=
  (congrArg o.run (image_run m)).trans <| (run_through_leaves o m suffixFuel).trans <|
    bind_congr_of_forall_mem_support coinTape (after_coins o m)

theorem committed_root (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    (Artifact.submission.readCommit (endCommit o m ws)).1 =
      Late.node (Binary.treeM (M:=Id) o.compression m (wordTape ws)) LOG_LENGTH 0 := by
  obtain ⟨_,cm,tree,_⟩:=before_spec o m ws len
  change readBuffer (exited _) rootDestination 32=_
  rw [exited_root _ cm,show rootSource=nodeAddress LOG_LENGTH 0 by decide]
  apply (tree.nodes LOG_LENGTH (by decide) 0 (by decide)).trans
  exact (fixed_tree_node _ _ _ _ _ le_rfl (by decide)).symm
end CommitGolfCandidate.Chained.BinaryMachine
