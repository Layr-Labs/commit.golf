import CommitGolfCandidate.K1Manifest
import CommitGolfCandidate.K3CUUnits
import CommitGolfCandidate.QuartetPhysicalInputs

namespace TwoPermutationPrototype.Grouped
open CommitGolf

abbrev actual := K1Artifact.submission

/-- Key word `j` (key block words 1..3) of a trapdoor. -/
def savedKey {n : Nat} (td : BitVec n) (j : Fin 3) := td.extractLsb' (8*(4831838216+8*j.val)) 64

end TwoPermutationPrototype.Grouped
