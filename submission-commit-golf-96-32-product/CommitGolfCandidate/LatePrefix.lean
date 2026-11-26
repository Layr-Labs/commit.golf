import CommitGolfCandidate.LateReady
import CommitGolfCandidate.LateCoins

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def words : ProbComp (List PairCoins) :=
  (List.range (LENGTH/2)).mapM fun _ => ($ᵗ PairCoins : ProbComp PairCoins)

attribute [local irreducible] List.range

theorem words_length (ws : List PairCoins) (member : ws ∈ support words) : ws.length = pairCount := by
  have lengthMap {α β : Type} (xs : List α) (f : α → ProbComp β) (ys : List β)
      (reach : ys ∈ support (xs.mapM f)) : ys.length = xs.length := by
    induction xs generalizing ys with
    | nil => simpa using reach
    | cons x xs ih =>
      simp only [List.mapM_cons, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reach
      obtain ⟨b,_,tail,mem,rfl⟩ := reach
      simp only [List.length_cons, ih _ mem]
  unfold words at member
  exact (lengthMap (List.range (LENGTH/2)) (fun _ => ($ᵗ PairCoins : ProbComp PairCoins)) ws member).trans List.length_range

def leavesDone (o : Oracle) (m : Message) (ws : List PairCoins) :=
  leafFold o.compression LENGTH 0 (ready (sampled m ws))

theorem leaves_done_contents (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    LeafContents o.compression m (wordTape ws) LENGTH (leavesDone o m ws) := by
  simpa only [Nat.zero_add,leavesDone] using leaf_fold_contents o.compression m (wordTape ws) LENGTH 0 _
    (hash_start m ws len) (ready_contents m o.compression ws len) (le_of_eq (Nat.zero_add LENGTH))

theorem leaves_done_regs (o : Oracle) (m : Message) (ws : List PairCoins) (len : ws.length=pairCount) :
    AtLeaf (leavesDone o m ws) LENGTH := by
  simpa only [Nat.zero_add,leavesDone] using leaf_fold_registers o.compression LENGTH 0 _
    (hash_start m ws len) (le_of_eq (Nat.zero_add LENGTH))

attribute [local irreducible] commitImage execute leafFold

theorem run_through_leaves (o : Oracle) (m : Message) (fuel : Nat) :
    o.run (execute commitImage (16842768 + (9 + (leafSteps 0 LENGTH + fuel))) (startState m) true) =
      (do let ws ← words
          let (out,n) ← o.run (execute commitImage fuel (leavesDone o m ws) true)
          return (out.charge 741933081 67108864,67108864+n)) := by
  rw [commit_through_sampling _ rfl rfl, lift_draws, oracle_run_coins_bind]
  apply bind_congr_of_forall_mem_support
  intro ws reach
  have len := words_length ws reach
  let s := sampled m ws
  have head := apply_pairs_invariant ws 0 (setupState (startState m) 16)
    (setup_pair _ rfl rfl) (by omega)
  have pc : s.pc=pcAt 530 := by change (applyPairs 0 _ ws).pc = _; simpa only [Nat.zero_add,len,lt_self_iff_false,if_false] using head.pc
  change o.run (do let r ← execute commitImage (9+(leafSteps 0 LENGTH+fuel)) s true
                   return r.charge 67174416 0) = _
  rw [show 9+(leafSteps 0 LENGTH+fuel)=(fuel+leafSteps 0 LENGTH)+9 by omega,
    run_ready s pc,bind_assoc]
  simp only [pure_bind, oracle_run_bind, oracle_run_pure]
  rw [leaf_fold_run o LENGTH 0 (ready s) (hash_start m ws len) (by omega)]
  simp only [bind_assoc,pure_bind,Nat.add_zero,Execution.charge,← Nat.add_assoc]
  rfl

end CommitGolfCandidate.Late
