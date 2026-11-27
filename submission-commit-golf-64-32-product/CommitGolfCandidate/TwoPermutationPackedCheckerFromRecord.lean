import CommitGolfCandidate.TwoPermutationPackedCheckerObservation
import CommitGolfCandidate.TwoPermutationPackedCheckCapABI

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf RiscvZkvm.Rv64


theorem checker_facts_from_record (bound : Hybrid.C3PReplayBound238) (record : Oracle → Nat → Index → MachineState → RecordBlock)
    (verified : RecordRefines record) : PackedCertificate.CheckerFacts PackedChecker.submission :=
  checker_facts_of_observations bound (checker_complete_observation record verified checker_cap_facts)

end TwoPermutationPrototype.Packed.Checker
