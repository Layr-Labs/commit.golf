import CommitGolfCandidate.PairProgress
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 6000
set_option maxHeartbeats 120000
attribute [local irreducible] readBuffer checkEvaluation

private theorem leafCalls (o : Oracle) (n : Nat) (s : MachineState) :
    (checkEvaluation o (checkLeafLoop s n)).2=n := by
  induction n generalizing s with
  | zero => rw [checkLeafLoop,check_evaluation_pure]
  | succ k ih =>
    rw [checkLeafLoop,check_evaluation_public_bind]
    simp [ih,Nat.add_comm]

private theorem pathCalls (o : Oracle) (n : Nat) (s : MachineState) :
    (checkEvaluation o (rec_checkPathLoop s n)).2=n := by
  induction n generalizing s with
  | zero => rw [rec_checkPathLoop,check_evaluation_pure]
  | succ k ih =>
    rw [rec_checkPathLoop,check_evaluation_public_bind]
    simp [ih,Nat.add_comm]

theorem recordCalls (o : Oracle) (s : MachineState) :
    (checkEvaluation o (rec_checkPositionHash s 16)).2=20 := by
  simp only [rec_checkPositionHash,check_evaluation_bind,check_evaluation_pure,checkLeafSubroutineRun,leafCalls,pathCalls]
  exact congrArg (fun t : Digest × Nat => t.2+3+(16+0))
    (check_evaluation_public o (.inl (leafQuery (checkLeafInitCopyState (rec_checkPositionState s)))))

theorem upperCalls (o : Oracle) (n : Nat) (s : MachineState) :
    (checkEvaluation o (top_checkCapParentLoop s n)).2=n := by
  induction n generalizing s with
  | zero => rw [top_checkCapParentLoop,check_evaluation_pure]
  | succ k ih =>
    rw [top_checkCapParentLoop,check_evaluation_public_bind]
    simp [ih,Nat.add_comm]

theorem upperRoot (o : Oracle) (s : MachineState) (cap : Nat → Digest)
    (a : s.getReg .x10=8640) (d : s.getReg .x12=4576)
    (slots : ∀ p<128,readBuffer s (4608+32*p) 32=cap p) :
    readBuffer (checkEvaluation o (top_checkCapParentLoop s 127)).1 544 32 =
      referenceHeap o.compression 128 cap 1 := by
  apply top_cap_parent_loop_heap o s cap 127 (by decide) a d _ 1 (by decide) (by decide)
  intro i lo hi
  let p := i-128
  have bp : p<128 := by dsimp [p]; omega
  have eqn : 128+p=i := by dsimp [p]; omega
  have leaf := reference_heap_leaf o.compression 128 cap p bp
  rw [eqn] at leaf
  rw [leaf,show 512+32*i=4608+32*p by omega]
  exact slots p bp
end CommitGolfCandidate.PairCap.Batch
