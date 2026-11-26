import CommitGolfCandidate.S5LeafReady
import CommitGolfCandidate.S5LeafLoop
import CommitGolfCandidate.LateCoins

namespace CommitGolfCandidate.S5Machine
open CommitGolfCandidate.Late (PairCoins lift_draws)
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def coinTape : ProbComp (List PairCoins) :=
  (List.range (LENGTH/2)).mapM fun _ => ($ᵗ PairCoins : ProbComp PairCoins)

attribute [local irreducible] List.range

theorem words_length (ws : List PairCoins) (member : ws ∈ support coinTape) : ws.length = pairCount := by
  have lengthMap {α β : Type} (xs : List α) (f : α → ProbComp β) (ys : List β)
      (reach : ys ∈ support (xs.mapM f)) : ys.length = xs.length := by
    induction xs generalizing ys with
    | nil => simpa using reach
    | cons x xs ih =>
      simp only [List.mapM_cons, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reach
      obtain ⟨b,_,tail,mem,rfl⟩ := reach
      simp only [List.length_cons, ih _ mem]
  unfold coinTape at member
  exact (lengthMap (List.range (LENGTH/2)) (fun _ => ($ᵗ PairCoins : ProbComp PairCoins)) ws member).trans List.length_range

def leavesDone (o : Oracle) (m : Message) (ws : List PairCoins) :=
  leafFold o.compression LENGTH 0 (prepareLeaves (sampled m ws))

theorem ready_contents (m : Message) (H : Compression) (ws : List PairCoins) (len : ws.length=pairCount) :
    LeafContents H m (wordTape ws) 0 (prepareLeaves (sampled m ws)) := by
  have mem (q : MachineState) : (prepareLeaves q).mem=q.mem := rfl
  exact contents_congr (mem _) (sampled_contents m H ws len)

theorem leaves_done_contents (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    LeafContents o.compression m (wordTape ws) LENGTH (leavesDone o m ws) := by
  simpa only [Nat.zero_add,leavesDone] using leaf_fold_contents o.compression m (wordTape ws) LENGTH 0 _
    (leaf_initial m ws len) (ready_contents m o.compression ws len) (le_of_eq (Nat.zero_add LENGTH))

theorem leaves_done_regs (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    AtLeaf (leavesDone o m ws) LENGTH := by
  simpa only [Nat.zero_add,leavesDone] using leaf_fold_registers o.compression LENGTH 0 _
    (leaf_initial m ws len) (le_of_eq (Nat.zero_add LENGTH))

attribute [local irreducible] execute leafFold
theorem run_through_leaves (o : Oracle) (m : Message) (fuel : Nat) :
    o.run (execute commitImage (fuel+219951127) (start m) true)=
      (do let ws←coinTape;let (out,n)←o.run (execute commitImage fuel (leavesDone o m ws) true)
          return (out.charge 740044823 67108864,67108864+n)) := by
  have steps : leafSteps 0 LENGTH=203161599 := by decide
  have price : leafCycles 0 LENGTH=672923647 := by decide
  rw [show fuel+219951127=((fuel+leafSteps 0 LENGTH)+13)+16789515 by omega,commit_sampling,draws,lift_draws,oracle_run_coins_bind]
  apply bind_congr_of_forall_mem_support
  intro ws mem
  have len:=words_length ws mem
  rw [leaf_entry_run _ (sampled_pc m ws len),bind_assoc]
  simp only [pure_bind,oracle_run_bind,oracle_run_pure]
  rw [leaf_fold_run o LENGTH 0 _ (leaf_initial m ws len) (by omega),price]
  simp only [bind_assoc,pure_bind,Nat.add_zero,Execution.charge,←Nat.add_assoc]
  rfl
end CommitGolfCandidate.S5Machine
