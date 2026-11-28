import CommitGolfCandidate.C3PTranscript
import CommitGolfCandidate.C3PAdmission

/-! # The paired opener's facts and the commit's resources. -/

namespace TwoPermutationPrototype.PackedCertificate
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling

-- Sequential elaboration, as in C3PAdmission (the verifier builds with parallel elaboration on two CPUs).
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem commit_trace_resources (initial : RiscvZkvm.Rv64.MachineState) (r : Execution)
    (h : r ∈ support (RV64.C3P.commitTraceP initial)) :
    r.exit = .success ∧ r.cycles = 1266820207 ∧ r.oracleCalls = 83886079 := by
  unfold RV64.C3P.commitTraceP at h
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

theorem commit_resources_of (s : Submission) (lay : RV64.C3P.PairedCommitLayout s) (message : Message)
    (result : Execution) (reachable : result ∈ support (s.run .commit message)) :
    result.exit = .success ∧ result.cycles = 1266820207 ∧ result.oracleCalls = 83886079 := by
  have run : s.run .commit message = RV64.C3P.commitTraceP (s.initialState .commit message) := by
    change execute (s.image .commit) (s.steps .commit) (s.initialState .commit message) true = _
    rw [lay.image, show s.steps .commit = 276964470 + (s.steps .commit - 276964470) by
      have := lay.fuel; omega]
    exact RV64.C3P.paired_commit_execution _ (RV64.C3P.paired_commit_entry _ lay message) _
  rw [run] at reachable
  exact commit_trace_resources _ result reachable

theorem paired_commit_resources (message : Message) (result : Execution)
    (reachable : result ∈ support (pairedSubmission.run .commit message)) :
    result.exit = .success ∧ result.cycles = 1266820207 ∧ result.oracleCalls = 83886079 :=
  commit_resources_of pairedSubmission paired_commit_layout message result reachable

theorem paired_read_proof_length (s : Submission) (result : Execution) (succeeded : s.openingSucceeded result = true) :
    (s.readProof result).length = (result.state.getReg .x11).toNat := by
  simp only [Submission.readProof, succeeded, ite_true, List.length_map, List.length_range]

theorem paired_opening_facts : OpeningFacts pairedSubmission where
  runs trapdoor positions result reached := by
    have abi := paired_opening_abi
    by_cases empty : positions.card = 0
    · obtain ⟨r, run, physical⟩ := PackedOpening.opening_empty_run pairedSubmission abi trapdoor positions empty
      rw [run, support_pure, Set.mem_singleton_iff] at reached
      subst reached
      refine ⟨physical.success, PackedOpening.opening_success pairedSubmission abi trapdoor positions _ physical,
        by rw [physical.noCalls]; exact Nat.zero_le _, fun batch => ?_⟩
      have : positions.card = 128 := batch
      omega
    · obtain ⟨P, ys, ended, success, cycles, calls, rest⟩ :=
        PackedOpening.paired_opening_support pairedSubmission abi trapdoor positions (by omega) result reached
      have fit : (result.state.getReg .x11).toNat ≤ pairedSubmission.sizes.proof := by
        rw [rest.length]
        exact (PackedOpening.proof_fits_every_cardinality positions).trans abi.capacity
      have succeeded : pairedSubmission.openingSucceeded result = true := by
        simp [Submission.openingSucceeded, success, fit]
      refine ⟨success, succeeded, by rw [calls]; unfold OPEN_BUDGET; omega, fun batch => ?_⟩
      obtain ⟨cyc, bytes⟩ := PackedOpening.scheduled_scored_limits positions batch
      have size : positions.card = 128 := batch
      refine ⟨?_, ?_⟩
      · rw [cycles]
        unfold PackedOpening.scheduledCycles at cyc
        unfold PackedOpening.restCycles PackedOpening.Prepass.prepassCycles
        rw [ite_eq_right (by omega)] at cyc
        rw [size] at cyc ⊢
        omega
      · rw [paired_read_proof_length _ _ succeeded, rest.length]
        exact bytes
  refines := PackedOpening.paired_transcript_refines pairedSubmission paired_commit_layout paired_opening_abi

end TwoPermutationPrototype.PackedCertificate
