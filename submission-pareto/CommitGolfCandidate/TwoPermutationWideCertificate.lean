import CommitGolfCandidate.TwoPermutationGenericCertificate
import CommitGolfCandidate.TwoPermutationWideCommit

namespace TwoPermutationPrototype.WideCertificate
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def wideSubmission : Submission where
  sizes := ⟨1610612736, 8858378240⟩
  layout := ⟨4096, 4294971392, 4294971424, 5905584160, 6039801952, 10334769248⟩
  steps
    | .commit => 1073807360
    | .opening => 8590000128
    | .check => 17179934720
  image
    | .commit => RV64.wideCommitImage
    | .opening => Opening.openingImage
    | .check => Artifact.submission.image .check

theorem wide_submission_matches_artifact : wideSubmission = Artifact.submission := by
  have images : wideSubmission.image = Artifact.submission.image := by
    funext program
    cases program with
    | commit => exact RV64.wide_manifest_image
    | opening => rfl
    | check => rfl
  change (Submission.mk wideSubmission.sizes wideSubmission.layout wideSubmission.image wideSubmission.steps) =
    (Submission.mk wideSubmission.sizes wideSubmission.layout Artifact.submission.image wideSubmission.steps)
  exact congrArg (fun image => Submission.mk wideSubmission.sizes wideSubmission.layout image wideSubmission.steps) images

private theorem wide_opening_abi : Opening.OpeningABI wideSubmission where
  toOpeningLayout := ⟨rfl, rfl, rfl, rfl⟩
  image := rfl
  capacity := Nat.le_refl _
  fuel := Nat.le_refl _

private theorem wide_admitted : wideSubmission.Admission := by
  intro program
  cases program with
  | commit =>
    change (RV64.wideCommitImage.byteSize < MAX_PROGRAM_BYTES ∧
      LayoutValid (wideSubmission.layout.buffers wideSubmission.sizes) RV64.wideCommitImage) ∧ _
    have size : RV64.wideCommitImage.byteSize < MAX_PROGRAM_BYTES := by
      rw [RV64.wide_manifest_image]
      simp only [Artifact.submission, Image.byteSize, ArtifactEncoding.length_decode]
      decide
    exact ⟨⟨size, by decide⟩, by decide⟩
  | opening => decide
  | check => decide

private theorem wide_commit_resources (leaves : RV64.WideLeafExecution) (message : Message)
    (result : Execution) (reached : result ∈ support (wideSubmission.run .commit message)) :
    result.exit = .success ∧ result.cycles = 671613340 ∧ result.oracleCalls = 50331647 := by
  have entry : RV64.CommitEntry (wideSubmission.initialState .commit message) :=
    ⟨rfl,rfl,rfl,rfl⟩
  erw [RV64.submission_wide_commit_run leaves wideSubmission rfl
    (by decide) message entry] at reached
  simp only [RV64.wideCommitTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨salts,_,state,_,rfl⟩ := reached
  exact ⟨rfl,rfl,rfl⟩

theorem wide_certificate (leaves : RV64.WideLeafExecution)
    (committed : Opening.CommitTranscript wideSubmission) (checks : CheckerFacts wideSubmission) :
    Certificate wideSubmission 71680 671613340 42744 :=
  certificate_of_refinements (wide_commit_resources leaves) wide_opening_abi
    wide_admitted committed checks

end TwoPermutationPrototype.WideCertificate
