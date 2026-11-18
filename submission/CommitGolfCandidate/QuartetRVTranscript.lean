import CommitGolfCandidate.QuartetRVProofBytes
import CommitGolfCandidate.QuartetRVRecords
import CommitGolfCandidate.QuartetRVRecordRun

namespace TwoPermutationPrototype.QuartetRV
open CommitGolf CommitGolf.Riscv CommitGolfCandidate OracleComp Sampling
open Opening (trapdoorHeap)
open Sampling.Quartet (abstract_reference_hiding concrete_hiding_of_refinement upperHeap quartetLookup QuartetRefines builder)
set_option maxRecDepth 8192
local instance QuartetRVTranscriptLocalInstance1 {α : Type} : MeasurableSpace α := ⊤

theorem manifest_abi : OpeningABI QuartetArtifact.submission :=
  ⟨manifest_layout, image_actual, by decide, by decide⟩

theorem opening_physical (s : Submission) (abi : OpeningABI s) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) :
    ∃ result, s.run .opening (trapdoor,positions) = pure result ∧ OpenPhysical s trapdoor positions result :=
  opening_physical_with (execute_records_from_step execute_record) s abi trapdoor positions

theorem scheme_open_bytes (s : Submission) (abi : OpeningABI s) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) :
    s.scheme.opening trapdoor positions = pure (proofFromTrapdoor (s:=s) trapdoor positions) :=
  scheme_open_bytes_with (execute_records_from_step execute_record) s abi trapdoor positions

theorem proof_size (s : Submission) (abi : OpeningABI s) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (result : Execution) (physical : OpenPhysical s trapdoor positions result) :
    (s.readProof result).length = (result.state.getReg .x11).toNat := by
  simp only [Submission.readProof, opening_success s abi trapdoor positions result physical,
    ite_true,List.length_map,List.length_range]

theorem actual_opening_attainment (trapdoor : BitVec (8*QuartetArtifact.submission.sizes.trapdoor)) :
    ∃ (positions : Positions) (result : Execution), positions.card=BATCH ∧
      QuartetArtifact.submission.run .opening (trapdoor,positions) = pure result ∧
      result.cycles=93945 ∧ (QuartetArtifact.submission.readProof result).length=72192 := by
  obtain ⟨p,k,fuel,bytes⟩ := QuartetOpening.scored_attainment
  obtain ⟨r,run,correct⟩ := opening_physical QuartetArtifact.submission manifest_abi trapdoor p
  exact ⟨p,r,k,run,correct.cycles.trans fuel,
    (proof_size _ manifest_abi trapdoor p r correct).trans (correct.length.trans bytes)⟩

theorem actual_opening_bounds (trapdoor : BitVec (8*QuartetArtifact.submission.sizes.trapdoor))
    (positions : Positions) (k : positions.card = BATCH) :
    ∃ result : Execution, QuartetArtifact.submission.run .opening (trapdoor,positions) = pure result ∧
      result.exit = .success ∧ result.oracleCalls = 0 ∧ result.cycles ≤ 93945 ∧
      (QuartetArtifact.submission.readProof result).length ≤ 72192 := by
  obtain ⟨r,run,correct⟩ := opening_physical QuartetArtifact.submission manifest_abi trapdoor positions
  obtain ⟨fuel,bytes⟩ := QuartetOpening.scored_limits positions k
  exact ⟨r,run,correct.success,correct.noCalls,correct.cycles.le.trans fuel,
    ((proof_size _ manifest_abi trapdoor positions r correct).trans correct.length).le.trans bytes⟩

/-- The opening-machine component is unconditional. Only the commit distribution and its three stored slices
remain in the implementation refinement. -/
theorem transcript_refines (s : Submission) (abi : OpeningABI s)
    (trapdoorOf : Oracle → Message → CompleteSaltTape → BitVec (8*s.sizes.trapdoor))
    (distribution : ∀ oracle message, fixedOracleRun oracle (s.scheme.commit message) =ᵈ
      (do let salts ← sampleCompleteSaltTape
          let p := BiPermutation.equiv Block oracle.permutation
          let leaves := pinnedFullLeafDigests p message salts
          pure (upperHeap (quartetLookup p) oracle.compression leaves 1, trapdoorOf oracle message salts)))
    (nonce : ∀ oracle message salts i, trapdoorSalt (s:=s) (trapdoorOf oracle message salts) i = salts i)
    (leaf : ∀ oracle message salts (i : Index), trapdoorLeaf (s:=s) (trapdoorOf oracle message salts) i.val =
      pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts i)
    (heap : ∀ oracle message salts node, 0<node → node<2*(LENGTH/4) →
      trapdoorHeap (s:=s) (trapdoorOf oracle message salts) node =
      upperHeap (quartetLookup (BiPermutation.equiv Block oracle.permutation)) oracle.compression
        (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts) node) :
    QuartetRefines s.scheme builder := by
  intro oracle message positions
  unfold executableTranscript
  rw [fixed_oracle_run_bind]
  apply ((distribution oracle message).bind_left _).trans
  simp only [bind_assoc,pure_bind]
  apply EvalDistEq.bind_right
  intro salts
  rw [scheme_open_bytes s abi,pure_bind,fixed_oracle_run_pure]
  have proof := proof_from_trapdoor_matches s (trapdoorOf oracle message salts) positions
    (quartetLookup (BiPermutation.equiv Block oracle.permutation)) oracle.compression
    (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)
    salts (heap oracle message salts) (leaf oracle message salts) (nonce oracle message salts)
  rw [proof]
  rfl

end TwoPermutationPrototype.QuartetRV
