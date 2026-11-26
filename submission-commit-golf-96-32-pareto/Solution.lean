import CommitGolfCandidate.R4Commit
import CommitGolfCandidate.R4Contract
namespace CommitGolf.Challenge
open CommitGolfCandidate.R4
def submission := Artifact.submission
theorem submission_matches_artifact : submission=CommitGolf.Artifact.submission:=rfl
theorem certificate : Certificate submission 70080 847964651 65222 := by
  apply certified
  intro o m
  obtain ⟨s,run,contents⟩:=commitExact o m
  exact ⟨s,run,fun r=>⟨(contents r).root,(contents r).trapdoor⟩⟩
end CommitGolf.Challenge
