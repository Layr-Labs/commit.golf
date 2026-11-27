import CommitGolfCandidate.C3PCheckLeaf
import CommitGolfCandidate.C3PReplayBound
import CommitGolfCandidate.TwoPermutationPackedCertificate
import CommitGolfCandidate.TwoPermutationPackedCheckerFromRecord
import CommitGolfCandidate.TwoPermutationPackedRecordComposition
import CommitGolfCandidate.TwoPermutationPackedLowerAdapter
import CommitGolfCandidate.TwoPermutationPackedLevel

/-! # The paired checker's facts: the leader's record composition with the paired leaf block. -/
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf RiscvZkvm.Rv64
open TwoPermutationPrototype.Sampling (C3PReplayBound)

theorem paired_checker_facts (bound : C3PReplayBound) : PackedCertificate.CheckerFacts PackedChecker.submission :=
  checker_facts_from_record bound (joinedRecord C3PRecordLeaf.c3pBlock (adaptLowerStep levelResult))
    (joined_record_refines _ _ C3PRecordLeaf.c3p_leaf_block (lower_step_from_level levelResult levelFacts))

end TwoPermutationPrototype.Packed.Checker
