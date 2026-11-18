import CommitGolfCandidate.GroupedQFrame
import CommitGolfCandidate.TwoPermutationHeapInvariant
namespace TwoPermutationPrototype.Grouped
open TwoPermutationPrototype.QuartetCommit (qSource qUpper qLeaf PaddedLeaves quad_input_words quadWords)
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] checkEvaluation qAfter packBuffer

theorem q_units_content (oracle : Oracle) (before : Memory) (children : Nat → Words 4) (s : MachineState) (g count : Nat)
    (limit : g+count≤4194304) (ready : PaddedLeaves before children) (inv : QuadPrefix oracle before children s g) :
    QuadPrefix oracle before children (checkEvaluation oracle (qUnits count g s)).1 (g+count) := by
  induction count generalizing s g with
  | zero => simpa only [qUnits,check_evaluation_pure,Nat.add_zero] using inv
  | succ n ih =>
    simp only [qUnits,CommitGolfCandidate.check_evaluation_public_bind]
    rw [show g+(n+1)=g+1+n by omega]
    exact ih _ (g+1) (by omega) (quad_prefix_step oracle before children s g (by omega) ready inv)

private theorem qprefix_setpc (oracle : Oracle) (before : Memory) (children : Nat → Words 4) (s : MachineState)
    (n : Nat) (pc : Word) (r : QuadPrefix oracle before children s n) : QuadPrefix oracle before children (s.setPC pc) n :=
  ⟨r.upper,r.high⟩

attribute [local irreducible] qUnits

theorem q_groups_content (oracle : Oracle) (before : Memory) (children : Nat → Words 4) (s : MachineState) (k count : Nat)
    (limit : k+count≤512) (ready : PaddedLeaves before children) (inv : QuadPrefix oracle before children s (8192*k)) :
    QuadPrefix oracle before children (checkEvaluation oracle (qGroups count k s)).1 (8192*(k+count)) := by
  induction count generalizing s k with
  | zero => simpa only [qGroups,check_evaluation_pure,Nat.add_zero] using inv
  | succ n ih =>
    rw [qGroups,check_evaluation_bind,show k+(n+1)=k+1+n by omega]
    apply ih _ (k+1) (by omega)
    have step := q_units_content oracle before children s (8192*k) 8192 (by omega) ready inv
    rw [Nat.mul_succ]
    exact qprefix_setpc _ _ _ _ _ _ step

theorem q_units_counted (oracle : Oracle) (s : MachineState) (g count : Nat) : RunPublic oracle (qUnits count g s) count := by
  induction count generalizing s g with
  | zero => rw [qUnits];exact run_pure_public ..
  | succ n ih =>
    rw [qUnits,show n+1=1+n by omega]
    exact run_bind_public _ _ _ 1 n (run_query_public ..) (fun _ => ih _ _)

theorem q_groups_counted (oracle : Oracle) (s : MachineState) (k count : Nat) : RunPublic oracle (qGroups count k s) (8192*count) := by
  induction count generalizing s k with
  | zero => exact run_pure_public ..
  | succ n ih =>
    rw [qGroups,show 8192*(n+1)=8192+8192*n by omega]
    exact run_bind_public _ _ _ 8192 _ (q_units_counted ..) (fun _ => ih _ _)

end TwoPermutationPrototype.Grouped
