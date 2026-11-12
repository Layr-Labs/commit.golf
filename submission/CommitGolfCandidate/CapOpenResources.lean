import CommitGolfCandidate.CapOpenProgramRun
import CommitGolfCandidate.CapBoundarySize

/-! All-input opening termination and scored-batch resource bounds follow
from the actual image run. These facts hold for every serialized trapdoor;
completeness, binding and hiding remain separate certificate obligations. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_open_loaded_batch_bytes
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (batch : positions.card = BATCH) :
    (capOpenLoadedBytes trapdoor positions).length ≤ 75776 := by
  have positive : 0 < positions.card := by rw [batch]; decide
  have boundary := cap_open_requested_boundary_bound positions positive
  rw [cap_open_loaded_bytes_length, batch]
  simp only [capOpenBoundaryDigests, List.length_map, BATCH]
  omega

theorem cap_open_result_batch_cycles
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (batch : positions.card = BATCH) :
    (capOpenNonemptyResult trapdoor positions).cycles ≤ 40395 :=
  cap_open_loaded_batch_cycles positions (by simpa only [BATCH] using batch)

private theorem oracle_pure (oracle : Oracle) {α : Type} (value : α) :
    oracle.run (pure value : OracleComp World α) = pure (value, 0) := by
  simp [Oracle.run]
  rfl

theorem cap_open_program_termination (oracle : Oracle)
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    (prEvent ((fun result => result.1.exit ≠ Exit.unfinished) <$>
      oracle.run (capProgram.run .opening (trapdoor, positions)))) = 1 := by
  by_cases empty : positions.card = 0
  · rw [cap_open_empty_program_run trapdoor positions empty, oracle_pure]
    simp [capOpenEmptyResult]
  · have positive : 0 < positions.card := Nat.pos_of_ne_zero empty
    rw [cap_open_nonempty_program_run trapdoor positions positive, oracle_pure]
    simp [capOpenNonemptyResult]

theorem cap_open_batch_resources (oracle : Oracle)
    (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (batch : positions.card = BATCH) :
    (prEvent ((fun result => result.1.exit = Exit.success ∧
      result.1.cycles ≤ 40395 ∧ result.2 = 0 ∧
      (capProgram.readProof result.1).length ≤ 75776) <$>
      oracle.run (capProgram.run .opening (trapdoor, positions)))) = 1 := by
  have positive : 0 < positions.card := by rw [batch]; decide
  rw [cap_open_nonempty_program_run trapdoor positions positive, oracle_pure]
  simp only [map_pure]
  simp only [cap_open_nonempty_read_proof trapdoor positions positive,
    cap_open_result_batch_cycles trapdoor positions batch,
    cap_open_loaded_batch_bytes trapdoor positions batch]
  simp [capOpenNonemptyResult]

theorem cap_program_proof_size : capProgram.scheme.ProofSize 75776 := by
  intro oracle message positions batch
  unfold Scheme.honest
  apply le_antisymm (prEvent_le_one _)
  apply le_prEvent_bind_of_forall_le_of_support _ (OracleComp.prEvent_true_eq_one _)
  rintro ⟨⟨root, trapdoor⟩, calls⟩ _
  dsimp only
  have positive : 0 < positions.card := by rw [batch]; decide
  rw [cap_open_nonempty_scheme_bytes trapdoor positions positive, oracle_pure]
  simp [cap_open_loaded_batch_bytes trapdoor positions batch]

end CommitGolfCandidate
