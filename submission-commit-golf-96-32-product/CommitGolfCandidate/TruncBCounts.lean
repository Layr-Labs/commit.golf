import CommitGolfCandidate.TruncBProgress
import CommitGolfCandidate.TruncUpper
namespace CommitGolfCandidate.Trunc.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 6000
set_option maxHeartbeats 120000
attribute [local irreducible] readBuffer Late.Check.Normal.checkEvaluation

theorem upperCalls (o : Oracle) (n : Nat) (s : MachineState) :
    (Late.Check.Normal.checkEvaluation o (Check.top_checkCapParentLoop s n)).2=n := by
  induction n generalizing s with
  | zero => rw [Check.top_checkCapParentLoop,Late.Check.Normal.check_evaluation_pure]
  | succ k ih =>
    rw [Check.top_checkCapParentLoop,Late.Check.Normal.check_evaluation_public_bind]
    simp [ih,Nat.add_comm]

theorem upperRoot (o : Oracle) (s : MachineState) (cap : Nat → Digest)
    (a : s.getReg .x10=8640) (d : s.getReg .x12=4576)
    (slots : ∀ p<128,readBuffer s (4608+32*p) 32=cap p) :
    readBuffer (Late.Check.Normal.checkEvaluation o (Check.top_checkCapParentLoop s 127)).1 544 32 =
      referenceHeap o.compression 128 cap 1 := by
  apply Check.top_cap_parent_loop_heap o s cap 127 (by decide) a d _ 1 (by decide) (by decide)
  intro i lo hi
  let p := i-128
  have bp : p<128 := by dsimp [p]; omega
  have eqn : 128+p=i := by dsimp [p]; omega
  have leaf := reference_heap_leaf o.compression 128 cap p bp
  rw [eqn] at leaf
  rw [leaf,show 512+32*i=4608+32*p by omega]
  exact slots p bp
end CommitGolfCandidate.Trunc.Batch
