import CommitGolfCandidate.QuartetChainCertificate
import CommitGolfCandidate.QuartetCommitTranscript
import CommitGolfCandidate.QuartetCommitCost

/-! Quartet + chain salts assembly (generator layer from submission c28dd9ca): every certificate field
except the four check-program facts (`CheckerFacts`) is discharged from the chain commit, opening and
hiding proofs. -/

namespace TwoPermutationPrototype.QuartetChainAssembly
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.QuartetChainCertificate
open TwoPermutationPrototype.QuartetCertificate (CheckerFacts)

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- The opening proofs name the manifest copy in `CommitGolfCandidate`; both values are
rendered from the same `programs.json`. -/
theorem manifest_eq : QuartetArtifact.submission = Artifact.submission := rfl

theorem quartet_admitted : Artifact.submission.Admission :=
  manifest_eq ▸ QuartetOpening.manifest_admitted

theorem quartet_opening_abi : QuartetRV.OpeningABI Artifact.submission :=
  manifest_eq ▸ QuartetRV.manifest_abi

theorem quartet_opening_facts : OpeningFacts Artifact.submission where
  runs trapdoor positions := by
    obtain ⟨result, run, physical⟩ :=
      QuartetRV.opening_physical Artifact.submission quartet_opening_abi trapdoor positions
    have successful :=
      QuartetRV.opening_success Artifact.submission quartet_opening_abi trapdoor positions result physical
    refine ⟨result, run, physical.success, successful, fun batch => ?_⟩
    have limits := QuartetOpening.scored_limits positions batch
    have length :=
      QuartetRV.proof_size Artifact.submission quartet_opening_abi trapdoor positions result physical
    exact ⟨physical.cycles.le.trans limits.1, (length.trans physical.length).le.trans limits.2⟩
  refines := QuartetCommit.commit_really_refines

theorem quartet_commit_resources (message : Message) (result : Execution)
    (reachable : result ∈ support (Artifact.submission.run .commit message)) :
    result.exit = .success ∧ result.cycles = 522614991 ∧ result.oracleCalls ≤ COMMIT_BUDGET := by
  obtain ⟨exit, cycles, calls⟩ := QuartetCommit.exact_cost message result reachable
  exact ⟨exit, cycles, calls.trans_le (by decide)⟩

theorem quartet_hiding :
    Artifact.submission.scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) :=
  QuartetCommit.actual_hiding

/-- The whole certificate, given the four check-program facts. -/
theorem quartet_certificate (checks : CheckerFacts Artifact.submission) :
    Certificate Artifact.submission 72192 522614991 93945 :=
  certificate_of_facts quartet_commit_resources quartet_admitted quartet_opening_facts checks quartet_hiding

end TwoPermutationPrototype.QuartetChainAssembly
