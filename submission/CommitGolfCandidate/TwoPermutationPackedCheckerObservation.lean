import CommitGolfCandidate.Layout2Observation
import CommitGolfCandidate.K1HideLeafBinding
import CommitGolfCandidate.QuadBinding

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (checkObservation checker_positions_bound)
open TwoPermutationPrototype.QuartetCertificate (honestCheckInput)
theorem checker_facts_of_observations
    (checked : ∀ (oracle : Oracle) (input : CheckInput),
      CheckerObservationFacts oracle input (checkObservation K1Artifact.submission oracle input)) :
    QuartetCertificate.CheckerFacts K1Artifact.submission := by
  refine ⟨fun oracle input => (checked oracle input).terminates,
    fun oracle input => (checked oracle input).queries.trans (by omega), ?_, ?_⟩
  · apply Quartet.quartet_scheme_binding _ k1_peer_leaf_layout_sharp
    intro oracle input
    dsimp only
    intro accepted
    have count := (checked oracle input).queries
    have card := checker_positions_bound input
    exact ⟨by omega,(checked oracle input).paths accepted⟩
  · intro oracle message positions salts
    exact (checked oracle (honestCheckInput oracle message positions salts)).honest message salts rfl

end TwoPermutationPrototype.Packed.Checker
