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

private theorem basePacked {n m : Nat} (code : ArtifactEncoding.Packed n) (bytes : ArtifactEncoding.Packed m) :
    dataBase ⟨ArtifactEncoding.decode 32 code,ArtifactEncoding.decode 8 bytes⟩=16*((MEMORY_BYTES-m)/16) := by
  simp only [dataBase,ArtifactEncoding.length_decode]

attribute [local irreducible] dataBase ArtifactEncoding.decode in
theorem openingDataBase : dataBase (submission.image .opening)=68719460304 :=
  basePacked Artifact.openingCode Artifact.openingData

theorem admission : submission.Admission := by
  intro p
  refine ⟨⟨?_,?_⟩,?_⟩
  · cases p
    · exact payloadSize Artifact.commitCode Artifact.commitData (by decide)
    · exact payloadSize Artifact.openingCode Artifact.openingData (by decide)
    · exact payloadSize Artifact.checkCode Artifact.checkData (by decide)
  · cases p with
    | commit => decide
    | opening => unfold LayoutValid;rw [openingDataBase];decide
    | check => decide
  · cases p <;> decide

end CommitGolfCandidate.Late
