import CommitGolfCandidate.TwoPermutationPackedCheckerObservation
import CommitGolfCandidate.TwoPermutationPackedCheckCapABI

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf RiscvZkvm.Rv64

theorem checker_facts_from_record (record : Oracle → Nat → Index → MachineState → RecordBlock)
    (verified : RecordRefines record) : QuartetCertificate.CheckerFacts PackedChecker.submission :=
  checker_facts_of_observations (checker_complete_observation record verified checker_cap_facts)

end TwoPermutationPrototype.Packed.Checker
