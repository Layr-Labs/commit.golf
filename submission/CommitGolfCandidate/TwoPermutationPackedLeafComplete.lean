import CommitGolfCandidate.TwoPermutationPackedLeafAdapter
import CommitGolfCandidate.TwoPermutationPackedRecordLeafPhysical

namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf RiscvZkvm.Rv64 TwoPermutationPrototype.Packed.Checker

theorem actual_leaf_block : LeafBlockRefines block := by
  intro oracle input ordinal present state fits cursor framed
  have exactRun := physical_facts oracle input ordinal present state fits cursor framed
  have short := leaf_steps_le (TwoPermutationPrototype.Checker.honestIndex input.positions ordinal present).val
  refine ⟨?_,exactRun.run,exactRun.cursor,exactRun.saved,exactRun.frame,?_,?_⟩
  · change leafSteps _ + (qCallSteps _ + 1 + 7) ≤ 208
    have quartet (t : MachineState) : qCallSteps t ≤ 129 := by unfold qCallSteps; split <;> omega
    have := quartet (rawLeaf oracle ordinal (TwoPermutationPrototype.Checker.honestIndex input.positions ordinal present).val state).1
    omega
  · exact block_trace oracle input ordinal present state fits cursor framed
  · exact block_honest oracle input ordinal present state fits cursor framed

end TwoPermutationPrototype.Packed.RecordLeaf
