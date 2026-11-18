-- Pair-heads copy of TwoPermutationPackedCheckerFromRecord (stack/check/work/mkcopy.py); edits below are marked PAIR.
import CommitGolfCandidate.PairCheckCheckerObservation
import CommitGolfCandidate.PairCheckNamespaces
import CommitGolfCandidate.PairCheckCheckCapABI

namespace TwoPermutationPrototype.PairCk.Packed.Checker
open  TwoPermutationPrototype.Packed TwoPermutationPrototype.Packed.Checker TwoPermutationPrototype.PairCk.Packed.Checker
open CommitGolf RiscvZkvm.Rv64

theorem checker_facts_from_record (even : Sampling.EvenLeafSmallBound)
    (record : Oracle → Nat → Index → MachineState → RecordBlock)
    (verified : RecordRefines record) : PairCertificate.PairCheckerFacts PairChecker.submission :=
  checker_facts_of_observations even (checker_complete_observation record verified checker_cap_facts)

end TwoPermutationPrototype.PairCk.Packed.Checker
