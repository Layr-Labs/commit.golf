-- Pair-heads copy of TwoPermutationPackedCheckerCertificate (stack/check/work/mkcopy.py); edits below are marked PAIR.
import CommitGolfCandidate.PairCheckCheckerFromRecord
import CommitGolfCandidate.PairCheckNamespaces
import CommitGolfCandidate.PairCheckRecordComposition
import CommitGolfCandidate.PairCheckLeafComplete
import CommitGolfCandidate.PairCheckLowerAdapter
import CommitGolfCandidate.PairCheckLevel
import CommitGolfCandidate.PairCheckPhases

namespace TwoPermutationPrototype.PairCk.Packed.Checker
open  TwoPermutationPrototype.Packed TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.PairCk.Packed.Checker
open CommitGolf RiscvZkvm.Rv64

/-! PAIR: the pair-heads checker facts. The leaf block is `RecordLeaf.block` (parity branch, odd path = A′'s leaf,
even path = words 494–542, whose execution facts are `EvenPathFacts`); the lower step is A′'s. -/

theorem pair_checker_facts_of_even_path (even : Sampling.EvenLeafSmallBound) (evenPath : RecordLeaf.EvenPathFacts) :
    PairCertificate.PairCheckerFacts PairChecker.submission :=
  checker_facts_from_record even (joinedRecord RecordLeaf.block (adaptLowerStep levelResult))
    (joined_record_refines RecordLeaf.block _ (RecordLeaf.actual_leaf_block evenPath)
      (lower_step_from_level levelResult levelFacts))

end TwoPermutationPrototype.PairCk.Packed.Checker
