import CommitGolfCandidate.TwoPermutationWideCertificate
import CommitGolfCandidate.TwoPermutationCheckerWideArtifact

namespace CommitGolf.Challenge

open TwoPermutationPrototype

def submission : CommitGolf.Submission := WideCertificate.wideSubmission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission :=
  WideCertificate.wide_submission_matches_artifact

theorem certificate : CommitGolf.Certificate submission 71680 638059030 42744 := by
  apply WideCertificate.wide_certificate
  rw [WideCertificate.wide_submission_matches_artifact]
  exact WideCertificate.artifact_checker_facts

end CommitGolf.Challenge
