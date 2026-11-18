import CommitGolfCandidate.CapHonestCheckInput
import CommitGolfCandidate.CapCommitBridge
import CommitGolfCandidate.CapOpenProgramRun

/-! Perfect completeness of the actual cap scheme. Commitment support comes
from its unchanged certified image; opening bytes and checker acceptance come
from the new images. Empty positions use the real zero-proof bypass. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv OracleComp
set_option autoImplicit false

private theorem scheme_commit (program : Submission) (message : Message) :
    program.scheme.commit message=program.readCommit <$> program.run .commit message := rfl

private theorem supported_nonempty (oracle : Oracle) (message : Message)
    (result : (Commitment × capProgram.scheme.Trapdoor) × Nat)
    (reachable : result ∈ support (oracle.run (capProgram.scheme.commit message)))
    (positions : Positions) (positive : 0 < positions.card) :
    (oracle.eval (capProgram.scheme.check result.1.1 positions
      (message.restrict positions) (capOpenLoadedBytes result.1.2 positions))).1=true := by
  change result ∈ support (oracle.run
    (capProgram.readCommit <$> (capProgram.run .commit message : OracleComp World Execution)))
    at reachable
  erw [oracle_run_map] at reachable
  simp only [support_map] at reachable
  obtain ⟨execution,reached,rfl⟩ := reachable
  exact cap_honest_nonempty_check oracle message execution.1.state
    (cap_commit_matches oracle message execution reached) positions positive

private theorem empty_accepts (oracle : Oracle) (root : Commitment)
    (message : Message) (positions : Positions) (empty : positions.card=0) :
    (oracle.eval (capProgram.scheme.check root positions
      (message.restrict positions) [])).1=true := by
  apply (cap_check_scheme_acceptance oracle
    ⟨root,positions,message.restrict positions,[]⟩).mpr
  simp [CapCheckProgramAccepts,empty]

theorem cap_program_completeness : capProgram.scheme.Completeness := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest,mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root,trapdoor⟩,commitCalls⟩,committed,rest⟩ := reached
  by_cases empty : positions.card=0
  · rw [cap_open_empty_scheme_bytes trapdoor positions empty,oracle_run_pure] at rest
    simp only [support_pure,Set.mem_singleton_iff] at rest
    obtain ⟨opened,rfl,rfl⟩ := rest
    exact empty_accepts oracle root message positions empty
  · have positive := Nat.pos_of_ne_zero empty
    rw [cap_open_nonempty_scheme_bytes trapdoor positions positive,oracle_run_pure]
      at rest
    simp only [support_pure,Set.mem_singleton_iff] at rest
    obtain ⟨opened,rfl,rfl⟩ := rest
    exact supported_nonempty oracle message ((root,trapdoor),commitCalls)
      committed positions positive

end CommitGolfCandidate
