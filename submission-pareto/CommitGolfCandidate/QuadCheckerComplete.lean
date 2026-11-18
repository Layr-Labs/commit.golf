import CommitGolfCandidate.QuadCheckerObservation
import CommitGolfCandidate.QuadRecordNodePhysical
import CommitGolfCandidate.QuadCheckCapABI

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (checkObservation)
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

/-- All checker facts for the actual quad3 image, with commit and opening images
left arbitrary for the final assembly. -/
theorem loader_checker_observation (oracle : Oracle) (input : CheckInput) :
    CheckerObservationFacts oracle input (checkObservation loaderReference oracle input) :=
  checker_complete_observation (joinedRecord RecordLeaf.block (adaptLowerStep levelResult))
    RecordLeaf.actual_record_refines checker_cap_facts oracle input

/-- This reference already runs the exact quad checker and production loader. -/
theorem loader_checker_facts : QuadCertificate.CheckerFacts loaderReference :=
  checker_facts_of_observations loaderReference loader_checker_observation

/-- The production layout of the quad3 checker (message, commitment, trapdoor,
indices, values, proof). -/
theorem loader_layout :
    loaderReference.layout = ⟨4096, 4294971392, 4294971424, 6761238560, 6895456352, 11190423648⟩ := rfl

/-- Final-image linking: only the actual checker dependencies are required. -/
theorem checker_facts (s : Submission)
    (capacity : s.sizes.proof = QUAD3_PROOF_CAPACITY)
    (layout : s.layout = loaderReference.layout)
    (code : s.image .check = quadCheckImage)
    (fuel : s.steps .check = 34359803904) : QuadCertificate.CheckerFacts s := by
  apply checker_facts_of_observations s
  intro oracle input
  have same := checker_reference_run s quadCheckImage quadCheckImage 10167000576 34359803904
    capacity layout code fuel input
  have observed : checkObservation s oracle input = checkObservation loaderReference oracle input := by
    unfold checkObservation
    rw [same]
    rfl
  rw [observed]
  exact loader_checker_observation oracle input

end TwoPermutationPrototype.Quad.Checker
