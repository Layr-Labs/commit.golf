import CommitGolfCandidate.QuartetChainAssembly
import CommitGolfCandidate.TwoPermutationPackedCheckerCertificate
import CommitGolfCandidate.TwoPermutationPinnedBindingCertificate

namespace CommitGolf.Challenge
open TwoPermutationPrototype

set_option maxRecDepth 65536
set_option exponentiation.threshold 2048

def submission : CommitGolf.Submission := CommitGolf.Artifact.submission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

/-- Quartet with paired permutation expansion: commit, opening and hiding from
`QuartetChainAssembly`, using the role-separated extension of c28dd9ca's chain replay proof;
the four check-program facts
(termination, query budget, binding through `Quartet.quartet_scheme_binding`, honest acceptance)
from the variant-B checker proof. -/
theorem certificate : CommitGolf.Certificate submission 72192 522614991 93945 :=
  QuartetChainAssembly.quartet_certificate (Packed.Checker.executable_checker_facts Sampling.pinned_replay_bound)

end CommitGolf.Challenge
