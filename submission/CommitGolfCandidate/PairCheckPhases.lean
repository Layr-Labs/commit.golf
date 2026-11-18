import CommitGolfCandidate.PairCheckCheckerFromRecord
import CommitGolfCandidate.PairCheckRecordComposition
import CommitGolfCandidate.PairCheckLowerAdapter
import CommitGolfCandidate.PairCheckLevel

/-! The pair-heads checker facts from any verified leaf block (`LeafBlockRefines`) and A′'s unchanged lower step. -/
namespace TwoPermutationPrototype.PairCk.Packed.Checker
open TwoPermutationPrototype.Packed TwoPermutationPrototype.Packed.Checker
open CommitGolf RiscvZkvm.Rv64

theorem pair_checker_from_phases (even : Sampling.EvenLeafSmallBound)
    (leaf : Oracle → Nat → Index → MachineState → RecordBlock) (leafVerified : LeafBlockRefines leaf) :
    PairCertificate.PairCheckerFacts PairChecker.submission :=
  checker_facts_from_record even (joinedRecord leaf (adaptLowerStep levelResult))
    (joined_record_refines leaf _ leafVerified (lower_step_from_level levelResult levelFacts))

end TwoPermutationPrototype.PairCk.Packed.Checker
