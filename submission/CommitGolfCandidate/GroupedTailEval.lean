import CommitGolfCandidate.GroupedPhysicalBase
import CommitGolfCandidate.GroupedQMeaning
import CommitGolfCandidate.QuartetPhysical
import CommitGolfCandidate.MaterializedManifest

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf qUpper digestWords originalLeaf physicalHeap upper_sequence_semantics upper_groups_semantics UpperContent PaddedLeaves physical_heap_parent physical_heap_leaf packed_sequence_keeps_output wide_parent_full_register)
open CommitGolfCandidate.Permutation.CounterSalt (salts)
set_option maxRecDepth 18000
set_option maxHeartbeats 1000000
attribute [local irreducible] readBuffer checkEvaluation qGroups qUnits scan fixedScan packedParentsTrace packedParentGroups rootPrefix physicalHeap originalLeaf readyState
def packedOutput (o : Oracle) (leaves : MachineState) : Execution :=
  ⟨.success,(checkEvaluation o (tailBody leaves)).1,519505181,43470847⟩

private theorem eval_three (o : Oracle) (a : OracleComp World MachineState) (b c : MachineState → OracleComp World MachineState) (f : MachineState → MachineState) :
    (checkEvaluation o (do let x ← a; let y ← b x; let z ← c y; pure (f z))).1 =
    f (checkEvaluation o (c (checkEvaluation o (b (checkEvaluation o a).1)).1)).1 := by
  simp only [check_evaluation_bind,check_evaluation_pure]

private theorem state_of_output (s : MachineState) :
    (⟨.success,s,519505181,43470847⟩ : Execution).state=s := rfl

private theorem output_eq (o : Oracle) (leaves : MachineState) :
    packedOutput o leaves=⟨.success,(checkEvaluation o (tailBody leaves)).1,519505181,43470847⟩ := rfl

attribute [local irreducible] packedOutput tailBody

theorem eval_tail (o : Oracle) (leaves : MachineState) :
    let quad := (checkEvaluation o (qGroups 512 0 (qStartPrefix leaves 3))).1
    let pre := (checkEvaluation o (packedParentsTrace 4194176 127 (upStartPrefix quad 6))).1
    let parents := (checkEvaluation o (packedParentGroups GroupedUpper.loopBase 32767 128 pre)).1
    (packedOutput o leaves).state=rootPrefix parents 10 := by
  refine (congrArg Execution.state (output_eq o leaves)).trans ((state_of_output _).trans ?_)
  unfold tailBody
  exact eval_three o (qGroups 512 0 (qStartPrefix leaves 3))
    (fun v => packedParentsTrace 4194176 127 (upStartPrefix v 6))
    (fun v => packedParentGroups GroupedUpper.loopBase 32767 128 v) (fun v => rootPrefix v 10)


end TwoPermutationPrototype.Grouped
