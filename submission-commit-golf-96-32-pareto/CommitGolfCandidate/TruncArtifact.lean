import CommitGolfCandidate.TruncImage
import CommitGolf.Artifact
namespace CommitGolfCandidate.Trunc
open CommitGolf
set_option maxRecDepth 200000 in
set_option maxHeartbeats 16000000 in
theorem matchesArtifact : submission=CommitGolf.Artifact.submission := rfl
end CommitGolfCandidate.Trunc
