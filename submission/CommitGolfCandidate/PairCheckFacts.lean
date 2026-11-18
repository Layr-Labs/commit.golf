import CommitGolfCandidate.PairCheckCheckerCertificate
import CommitGolfCandidate.PairCheckRecordLeafEven

/-! # Pair-heads checker facts

`pair_checker_facts`: the checker facts (termination, query budget, binding, honest acceptance) of the submission
whose check image is the frozen pair-heads checker (`PairChecker.submission`, rendered from
`stack/image/programs-ph-frozen.json`), given the even-leaf binding bound of the security lane
(`even_leaf_small_bound : EvenLeafSmallBound`). Transfer to the final artifact by check-image equality as in
`GroupedChecks.checker_facts`. -/

namespace TwoPermutationPrototype.PairCertificate

theorem pair_checker_facts (even : Sampling.EvenLeafSmallBound) : PairCheckerFacts PairChecker.submission :=
  PairCk.Packed.Checker.pair_checker_facts_of_even_path even PairCk.Packed.RecordLeaf.even_path_facts

end TwoPermutationPrototype.PairCertificate
