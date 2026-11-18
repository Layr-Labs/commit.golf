-- Pair-heads copy of TwoPermutationPackedLeafComplete (stack/check/work/mkcopy.py); edits below are marked PAIR.
import CommitGolfCandidate.PairCheckLeafAdapter
import CommitGolfCandidate.PairCheckNamespaces
import CommitGolfCandidate.PairCheckRecordLeafPhysical

namespace TwoPermutationPrototype.PairCk.Packed.RecordLeaf
open  TwoPermutationPrototype.Packed
open CommitGolf TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.PairCk.Packed.Checker

/-- PAIR: the pair-heads leaf block, given the even path's facts. -/
theorem actual_leaf_block (even : EvenPathFacts) : LeafBlockRefines block := by
  intro oracle input ordinal present state fits cursor framed
  have exactRun := physical_facts even oracle input ordinal present state fits cursor framed
  have stepBound : (block oracle ordinal (Checker.honestIndex input.positions ordinal present).val state).steps ≤ 206 := by
    change 22 + leafRunSteps _ + 132 ≤ 206
    unfold leafRunSteps
    split <;> omega
  refine ⟨stepBound,exactRun.run,exactRun.cursor,exactRun.saved,exactRun.frame,?_,?_⟩
  · exact block_trace even oracle input ordinal present state fits cursor framed
  · exact block_honest even oracle input ordinal present state fits cursor framed

end TwoPermutationPrototype.PairCk.Packed.RecordLeaf
