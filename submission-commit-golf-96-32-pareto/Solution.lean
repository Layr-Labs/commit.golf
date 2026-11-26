import CommitGolfCandidate.Stage3Certificate

namespace CommitGolf.Challenge
abbrev submission := CommitGolf.Artifact.submission
theorem submission_matches_artifact : submission=CommitGolf.Artifact.submission := rfl
theorem certificate : Certificate submission 69120 919142745 116041 := CommitGolfCandidate.Trunc.certificate
end CommitGolf.Challenge
