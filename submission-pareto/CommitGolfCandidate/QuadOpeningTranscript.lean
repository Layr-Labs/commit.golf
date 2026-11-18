import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.HidingDistribution
import CommitGolfCandidate.CompressionSampling
import CommitGolfCandidate.QuadOpeningProofBytes
import CommitGolfCandidate.QuadOpeningRecords
import CommitGolfCandidate.QuadOpeningRecordRun

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling OracleComp
open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces)
open QOpening (groupsBefore trapdoorHeap trapdoorSalt openingNodes cap_frontier_nodes_small cap_span_root)

local instance openingDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

theorem opening_physical (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) :
    ∃ result : Execution, s.run .opening (trapdoor, positions) = pure result ∧ OpenPhysical s trapdoor positions result :=
  opening_physical_with (execute_records_from_step execute_record) s abi trapdoor positions

theorem scheme_open_bytes (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) :
    s.scheme.opening trapdoor positions = pure (proofFromTrapdoor (s := s) trapdoor positions) :=
  scheme_open_bytes_with (execute_records_from_step execute_record) s abi trapdoor positions

theorem opening_proof_size (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (result : Execution) (physical : OpenPhysical s trapdoor positions result) :
    (s.readProof result).length = (result.state.getReg .x11).toNat := by
  simp only [Submission.readProof, opening_success s abi trapdoor positions result physical,
    ite_true, List.length_map, List.length_range]

theorem opening_scored_attainment (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) :
    ∃ (positions : Positions) (result : Execution), positions.card = BATCH ∧
      s.run .opening (trapdoor, positions) = pure result ∧
      result.cycles = 101371 ∧ (s.readProof result).length = 76800 := by
  obtain ⟨positions, count, cycleVal, byteVal⟩ := scheduled_scored_attainment
  obtain ⟨result, run, physical⟩ := opening_physical s abi trapdoor positions
  exact ⟨positions, result, count, run, physical.cycles.trans cycleVal,
    (opening_proof_size s abi trapdoor positions result physical).trans (physical.length.trans byteVal)⟩

/-- Compose the exact quad2 opener with the seed-keyed commit distribution supplied by the quad2
commit proof (`Quad2NonceCommitTranscript`). -/
theorem transcript_refines (s : Submission) (abi : OpeningABI s) (commit : Quad2NonceCommitTranscript s) :
    QuadNonceTranscriptRefines s.scheme quad2TranscriptBuilder := by
  intro oracle message positions
  unfold executableTranscript
  rw [fixed_oracle_run_bind]
  apply ((commit.distribution oracle message).bind_left _).trans
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro k
  rw [scheme_open_bytes s abi, pure_bind, fixed_oracle_run_pure]
  have proof := proof_from_trapdoor_matches s (commit.trapdoor oracle message k) positions
    oracle.compression (quadFunction oracle.permutation)
    (quadPublicLeaves oracle message (actualNonces oracle.permutation k)) (actualNonces oracle.permutation k)
    (fun node lo hi => commit.heap oracle message k node lo hi)
    (fun g inside => commit.quad oracle message k g inside)
    (fun index => commit.leaf oracle message k index)
    (fun index => commit.nonce oracle message k index)
  rw [proof]
  rfl

end TwoPermutationPrototype.QuadOpening
