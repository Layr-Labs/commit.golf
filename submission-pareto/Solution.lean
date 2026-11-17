import CommitGolfCandidate.TwoPermutationWideLeafMeaning
import CommitGolfCandidate.TwoPermutationCheckerWideArtifact

namespace CommitGolf.Challenge

open TwoPermutationPrototype

def submission : CommitGolf.Submission := WideCertificate.wideSubmission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission :=
  WideCertificate.wide_submission_matches_artifact

theorem certificate : CommitGolf.Certificate submission 71680 671613340 42744 := by
  apply WideCertificate.wide_certificate RV64.WideLeaves.executableLeaves
    (RV64.wideVerifiedTranscript RV64.WideLeaves.executableLeaves RV64.WideLeaves.executableMeaning)
  rw [WideCertificate.wide_submission_matches_artifact]
  exact WideCertificate.artifact_checker_facts

end CommitGolf.Challenge
