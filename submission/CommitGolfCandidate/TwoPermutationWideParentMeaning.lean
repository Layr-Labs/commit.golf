import CommitGolfCandidate.TwoPermutationWideParentControl
import CommitGolfCandidate.TwoPermutationParentBatchesContent
import CommitGolfCandidate.TwoPermutationCounted

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_pure check_evaluation_bind)

set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] checkEvaluation parentsTrace

theorem wide_parent_content (oracle : Oracle) (base : Word) (span groups : Nat)
    (state : MachineState) (heap : Nat → BitVec 256) (salts : Index → BitVec 128)
    (inside : span*groups < LENGTH)
    (tree : ∀ node, 0 < node → node < LENGTH →
      heap node = oracle.compression (heap (2*node+1) ++ heap (2*node)))
    (prior : ParentContent state heap salts (span*groups)) :
    ParentContent (checkEvaluation oracle (wideParentGroups base span groups state)).1 heap salts 0 := by
  induction groups generalizing state with
  | zero => simpa only [wideParentGroups, check_evaluation_pure, Nat.mul_zero] using prior
  | succ groups ih =>
    rw [Nat.mul_succ] at inside prior
    have body := parent_sequence_content oracle state heap salts (span*groups) span inside tree prior
    rw [wideParentGroups, check_evaluation_bind]
    apply ih _ (by omega)
    exact content_setpc _ _ heap salts (span*groups) body

theorem counted_wide_parents (oracle : Oracle) (base : Word) (span groups : Nat)
    (state : MachineState) :
    RunPublic oracle (wideParentGroups base span groups state) (span*groups) := by
  induction groups generalizing state with
  | zero => exact run_pure_public oracle state
  | succ groups ih =>
    rw [wideParentGroups, show span*(groups+1)=span+span*groups by rw [Nat.mul_succ, Nat.add_comm]]
    exact run_bind_public oracle _ _ span (span*groups) (counted_parents ..) (fun out => ih _)

end TwoPermutationPrototype.RV64
