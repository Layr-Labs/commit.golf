import CommitGolfCandidate.ChainedSeedContent
import CommitGolfCandidate.TwoPermutationCounted

/-! Fixed-oracle execution of the delivered commitment, including its private seed. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolfCandidate.Permutation.NonceChain
attribute [local irreducible] checkEvaluation parentLevels groups group batch

theorem counted_continuation_loop (oracle : Oracle) (buffer : Word) (remaining : Nat) (s : MachineState) :
    RunPublic oracle (loopTrace buffer remaining s) remaining := by
  induction remaining generalizing s with
  | zero => exact run_pure_public ..
  | succ remaining ih =>
    rw [loopTrace,show remaining+1 = 1+remaining by omega]
    exact run_bind_public _ _ _ 1 remaining (run_query_public ..) (fun _ => ih _)

theorem counted_continuation (oracle : Oracle) (base buffer : Word) (remaining : Nat) (s : MachineState) :
    RunPublic oracle (continuationFullTrace base buffer remaining s) remaining := by
  exact run_bind_public _ _ _ remaining 0 (counted_continuation_loop ..) (fun _ => run_pure_public ..)

theorem counted_hash (oracle : Oracle) (remaining : Nat) (s : MachineState) :
    RunPublic oracle (hashTrace remaining s) (remaining+1) := by
  rw [hashTrace,show remaining+1 = 1+remaining by omega]
  exact run_bind_public _ _ _ 1 remaining (run_query_public ..) (fun _ => counted_continuation ..)

theorem counted_native_node (oracle : Oracle) (h : Height) (s : MachineState) :
    RunPublic oracle (nodeTrace h s) (calls h) := by
  have count : calls h-1+1 = calls h := by have := calls_positive h; omega
  have hashed : RunPublic oracle (bodyHashTrace h s) (calls h) := by
    simpa only [bodyHashTrace,count] using counted_hash oracle (calls h-1) (bodyPrefix s h 3)
  have stored : RunPublic oracle (storeTrace h s) (calls h) :=
    run_bind_public _ _ _ (calls h) 0 hashed (fun _ => run_pure_public ..)
  exact run_bind_public _ _ _ (calls h) 0 stored (fun _ => run_pure_public ..)

theorem counted_native_level (oracle : Oracle) (h : Height) (remaining : Nat) (s : MachineState) :
    RunPublic oracle (levelTrace h remaining s) (calls h*remaining) := by
  induction remaining generalizing s with
  | zero =>
    rw [levelTrace]
    exact run_pure_public ..
  | succ remaining ih =>
    rw [levelTrace,Nat.mul_succ,Nat.add_comm (calls h*remaining) (calls h)]
    exact run_bind_public _ _ _ (calls h) _ (counted_native_node ..) (fun _ => ih _)

theorem counted_native_stage (oracle : Oracle) (h : Height) (s : MachineState) :
    RunPublic oracle (stageTrace h s) (stageQueries h) :=
  run_bind_public _ _ _ (calls h*heightCount h) 0 (counted_native_level ..) (fun _ => run_pure_public ..)

theorem counted_native_parents (oracle : Oracle) (remaining : Nat) (s : MachineState) :
    RunPublic oracle (parentLevels remaining s) (levelsQueries remaining) := by
  induction remaining generalizing s with
  | zero =>
    rw [parentLevels,levelsQueries]
    exact run_pure_public ..
  | succ remaining ih =>
    rw [parentLevels,levelsQueries]
    exact run_bind_public _ _ _ _ _ (counted_native_stage ..) (fun _ => ih _)

theorem counted_native_leaf (oracle : Oracle) (s : MachineState) (u : Fin 4096) (start index target : Nat) :
    RunPublic oracle (PackedLeaves.leafTrace s u start index target) 2 := by
  unfold PackedLeaves.leafTrace
  apply run_bind_public _ _ _ 1 1 (run_query_public ..)
  intro first
  exact run_bind_public _ _ _ 1 0 (run_query_public ..) (fun _ => run_pure_public ..)

theorem counted_native_unit (oracle : Oracle) (s : MachineState) (g u : Nat) :
    RunPublic oracle (unitTrace s g u) 2 :=
  run_bind_public _ _ _ 2 0 (counted_native_leaf ..) (fun _ => run_pure_public ..)

theorem counted_native_group (oracle : Oracle) (s : MachineState) (g count u : Nat) :
    RunPublic oracle (group g count u s) (2*count) := by
  induction count generalizing s u with
  | zero =>
    rw [group]
    exact run_pure_public ..
  | succ count ih =>
    rw [group,show 2*(count+1) = 2+2*count by omega]
    exact run_bind_public _ _ _ 2 _ (counted_native_unit ..) (fun _ => ih _ _)

theorem counted_native_batch (oracle : Oracle) (s : MachineState) (g : Nat) :
    RunPublic oracle (batch g s) 8192 := by
  unfold batch
  exact run_bind_public _ _ _ (2*4096) 0 (counted_native_group ..) (fun _ => run_pure_public ..)

theorem counted_native_groups (oracle : Oracle) (s : MachineState) (count g : Nat) :
    RunPublic oracle (groups count g s) (8192*count) := by
  induction count generalizing s g with
  | zero =>
    rw [groups]
    exact run_pure_public ..
  | succ count ih =>
    rw [groups,show 8192*(count+1) = 8192+8192*count by omega]
    exact run_bind_public _ _ _ 8192 _ (counted_native_batch ..) (fun _ => ih _ _)

theorem counted_commit_body (oracle : Oracle) (s : MachineState) :
    RunPublic oracle (chainedCommitBody s) 100857087 := by
  have parents (state : MachineState) : RunPublic oracle (completeParentTrace state) 67302655 := by
    have b := run_bind_public oracle (Fast.fast 8 (Fast.ctl state Fast.setup))
      (fun a => parentLevels 16 (Fast.ctl a Fast.handoff) >>= fun b => pure (chainedRootPrefix b 10)) _ _
      (Fast.fast_counted oracle 8 _)
      (fun a => run_bind_public _ _ _ _ 0 (counted_native_parents oracle 16 _) (fun _ => run_pure_public ..))
    have e : Fast.fastCalls 8 + (levelsQueries 16 + 0) = 67302655 := by decide +kernel
    rw [e] at b
    exact b
  have leaves : RunPublic oracle (leafPrefixTrace s) 33554432 :=
    run_bind_public _ _ _ (8192*2^12) 0 (counted_native_groups ..) (fun _ => run_pure_public ..)
  exact run_bind_public _ _ _ 33554432 67302655 leaves parents

def deliveredSeedOutput (oracle : Oracle) (message : Message) (key : Key) : Execution :=
  ⟨.success,(checkEvaluation oracle (chainedCommitBody (deliveredReady oracle message key))).1,1653371596,102382335⟩

theorem delivered_counted_run (oracle : Oracle) (message : Message) :
    oracle.run (Artifact.submission.run .commit message) =
      (do let key ← $ᵗ Key
          return (deliveredSeedOutput oracle message key,102382335)) := by
  rw [artifact_commit_run]
  unfold chainedCommitTrace
  rw [oracle_run_coins_bind]
  apply bind_congr
  intro key
  have expanded : oracle.run (Chain.expansion (Artifact.submission.initialState .commit message) key) =
      pure (Chain.evalChain oracle.permutation 0 (Chain.chainInitial (Artifact.submission.initialState .commit message) key)
        Chain.nonceChainCount,Chain.nonceChainCount) := Chain.chain_fixed_run ..
  rw [oracle_run_bind,expanded,pure_bind]
  simp only
  rw [oracle_run_bind,show oracle.run (chainedCommitBody _) = _ from counted_commit_body oracle _,pure_bind]
  simp only [oracle_run_pure,pure_bind]
  rfl

end CommitGolfCandidate.Chained.Native
