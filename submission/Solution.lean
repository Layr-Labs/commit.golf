import CommitGolfCandidate.QuartetChainAssembly
import CommitGolfCandidate.TwoPermutationPackedCheckerCertificate
import CommitGolfCandidate.TwoPermutationPinnedBindingCertificate

namespace CommitGolf.Challenge
open TwoPermutationPrototype

set_option maxRecDepth 65536
set_option exponentiation.threshold 2048

def submission : CommitGolf.Submission := CommitGolf.Artifact.submission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

/-- Quartet with permutation-chain salts: commit (with the chain-salt generator of submission
c28dd9ca), opening and hiding from `QuartetChainAssembly`; the four check-program facts
(termination, query budget, binding through `Quartet.quartet_scheme_binding`, honest acceptance)
from the variant-B checker proof. -/
theorem certificate : CommitGolf.Certificate submission 72192 523373526 93945 :=
  QuartetChainAssembly.quartet_certificate (Packed.Checker.executable_checker_facts Sampling.pinned_replay_bound)

end CommitGolf.Challenge
