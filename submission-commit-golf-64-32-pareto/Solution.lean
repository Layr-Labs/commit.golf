import CommitGolf.Artifact
import CommitGolfCandidate.ReconstructedAdmission
import CommitGolfCandidate.ReconstructedQueries
import CommitGolfCandidate.ReconstructedGenerator
import CommitGolfCandidate.ReconstructedEmpty
import CommitGolfCandidate.ReconstructedSeed
import CommitGolfCandidate.ReconstructedRadix
import CommitGolfCandidate.ReconstructedReturn
import CommitGolfCandidate.ReconstructedLeafLayout
import CommitGolfCandidate.ReconstructedCommitOutcome
import CommitGolfCandidate.ReconstructedLeafProjection
import CommitGolfCandidate.ReconstructedHonestProverScore
import CommitGolfCandidate.ReconstructedHonestProofSize
import CommitGolfCandidate.ReconstructedOpeningDelivery
import CommitGolfCandidate.ReconstructedCheckHonestChecker
import CommitGolfCandidate.ReconstructedCheckAcceptance

namespace CommitGolf.Challenge
open CommitGolfCandidate.Reconstruction

/-- The verifier generates this value directly from the delivered manifest. -/
def submission : CommitGolf.Submission := CommitGolf.Artifact.submission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := rfl

attribute [local irreducible] ArtifactEncoding.decode

theorem image_admission : submission.Admission := by
  apply admission_for_images submission rfl rfl rfl
  intro p
  cases p <;>
    simp only [submission, Artifact.submission, Riscv.Image.byteSize, ArtifactEncoding.length_decode] <;>
    decide

theorem machine_success : submission.MachineSuccess := HonestDelivery.machine OpeningDelivery.lower

theorem hiding_property : submission.scheme.Hiding HIDING_ERROR := HonestDelivery.secure OpeningDelivery.lower

theorem proof_size : submission.scheme.ProofSize 65544 := HonestProofSize.scored

theorem prover_cycles : submission.ProverCycles 1489523308 210404 := HonestProverScore.profile

theorem termination : submission.Termination :=
  CheckCertificateFields.termination CheckAcceptance.total

theorem completeness : submission.scheme.Completeness :=
  CheckCertificateFields.completeness CheckHonestChecker.verified

theorem honest_budgets : submission.scheme.HonestBudgets :=
  CheckCertificateFields.budgets CheckHonestChecker.verified

theorem position_binding : submission.scheme.Binding :=
  CommitGolfCandidate.Reconstruction.Binding.binding_of_accepted_paths submission CheckAcceptance.paths

theorem certificate : CommitGolf.Certificate submission 65544 1489523308 210404 where
  admission := image_admission
  machineSuccess := machine_success
  termination := termination
  completeness := completeness
  honestBudgets := honest_budgets
  proofSize := proof_size
  proverCycles := prover_cycles
  binding := position_binding
  hidingProperty := hiding_property

/-- The loader returns at most 65,544 bytes from the proved batch return path. -/
theorem batch_return_proof (s : RiscvZkvm.Rv64.MachineState) (positions : Positions)
    (batch : positions.card = BATCH)
    (cursor : (s.getReg .x7).toNat = Frontier.cursor (positions.sort (· ≤ ·)))
    (pc : s.pc = 10660) (sp : s.getReg .x2 = 68719474016)
    (ret : s.getMem 68719476328 = 4176) (fuel : Nat) :
    ∃ result : Riscv.Execution,
      Riscv.execute (submission.image .opening) (23+fuel) s true = pure result ∧
      result.exit = .success ∧ result.cycles = 23 ∧ (submission.readProof result).length ≤ 65544 := by
  obtain ⟨final, run, bytes⟩ := Return.batch_return s positions batch cursor pc sp ret fuel
  refine ⟨⟨.success, final, 23, 0⟩, run, rfl, rfl, ?_⟩
  unfold Submission.readProof
  split <;> simp_all only [List.length_map, List.length_range, List.length_nil, Nat.zero_le]

end CommitGolf.Challenge
