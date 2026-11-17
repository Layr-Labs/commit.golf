import CommitGolfCandidate.TwoPermutationHeaderAssembly

namespace TwoPermutationPrototype.WideCertificate
open CommitGolf Riscv TwoPermutationPrototype.Sampling

theorem verified_reference_checker : CheckerFacts Assembly.submission :=
  Checker.verifiedChecker

/-- The exact checker certificate links to any commit image with the
same checker ABI, proof limit, image and fuel. -/
theorem verified_checker (s : Submission)
    (proofCapacity : s.sizes.proof = Assembly.submission.sizes.proof)
    (layout : s.layout = Assembly.submission.layout)
    (code : s.image .check = Checker.checkerImage)
    (fuel : s.steps .check = Assembly.submission.steps .check) : CheckerFacts s :=
  checker_facts_of_run (Assembly.checker_reference_run s proofCapacity layout code fuel)
    verified_reference_checker

end TwoPermutationPrototype.WideCertificate
