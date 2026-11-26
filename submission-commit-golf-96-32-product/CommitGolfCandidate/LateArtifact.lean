import CommitGolf.Artifact
import CommitGolf.Statements
import CommitGolfCandidate.LateCode

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv

abbrev submission := Artifact.submission

private theorem payloadSize {n m : Nat} (code : ArtifactEncoding.Packed n) (data : ArtifactEncoding.Packed m)
    (bound : 4*n+m<MAX_PROGRAM_BYTES) :
    (⟨ArtifactEncoding.decode 32 code,ArtifactEncoding.decode 8 data⟩ : Image).byteSize<MAX_PROGRAM_BYTES := by
  simpa only [Image.byteSize,ArtifactEncoding.length_decode] using bound

theorem admission : submission.Admission := by
  intro p
  refine ⟨⟨?_,?_⟩,?_⟩
  · cases p
    · exact payloadSize Artifact.commitCode Artifact.commitData (by decide)
    · exact payloadSize Artifact.openingCode Artifact.openingData (by decide)
    · exact payloadSize Artifact.checkCode Artifact.checkData (by decide)
  · cases p <;> decide
  · cases p <;> decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem commit_image_matches : submission.image .commit = commitImage := by rfl

end CommitGolfCandidate.Late
