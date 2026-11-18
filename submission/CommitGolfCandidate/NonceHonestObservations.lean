import CommitGolfCandidate.NonceHonestProof
import CommitGolfCandidate.CapCompleteness
import CommitGolfCandidate.CapBudgets

/-! Acceptance and each stage's public query count agree with the original
honest game. Proof bytes change, and are bounded separately from this view. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 600000

theorem nonce_scheme_trapdoor :
    nonceCompressedProgram.scheme.Trapdoor = BitVec (8*capProgram.sizes.trapdoor) := rfl

theorem cap_scheme_trapdoor :
    capProgram.scheme.Trapdoor = BitVec (8*capProgram.sizes.trapdoor) := rfl

theorem nonce_honest_observe {α : Type} (observe : Bool → Nat → Nat → Nat → α)
    (oracle : Oracle) (message : Message) (positions : Positions) :
    (fun result : Scheme.HonestResult => observe result.accepted result.commitCalls result.openCalls result.checkCalls) <$>
      nonceCompressedProgram.scheme.honest oracle message positions=
    (fun result : Scheme.HonestResult => observe result.accepted result.commitCalls result.openCalls result.checkCalls) <$>
      capProgram.scheme.honest oracle message positions := by
  unfold Scheme.honest
  dsimp only [nonce_scheme_trapdoor, cap_scheme_trapdoor]
  simp only [map_bind,map_pure,nonce_compressed_commit_same]
  apply bind_congr_of_forall_mem_support
  rintro ⟨⟨root,trapdoor⟩,calls⟩ reached
  dsimp only
  have canonical := nonce_honest_commit_canonical oracle message ((root,trapdoor),calls) reached positions
  rw [nonce_delivered_scheme_opening trapdoor positions, nonce_old_scheme_opening trapdoor positions,
    oracle_run_pure, oracle_run_pure]
  simp only [pure_bind]
  rw [nonce_honest_check_eq trapdoor positions root _ canonical]

theorem nonce_compressed_completeness : nonceCompressedProgram.scheme.Completeness := by
  intro oracle message positions
  have observed:=congrArg prEvent (nonce_honest_observe (fun accepted _ _ _ => accepted=true) oracle message positions)
  exact observed.trans (cap_program_completeness oracle message positions)

theorem nonce_compressed_budgets : nonceCompressedProgram.scheme.HonestBudgets := by
  intro oracle message positions
  have observed:=congrArg prEvent (nonce_honest_observe
    (fun _ committed opened checked => committed ≤ COMMIT_BUDGET ∧
      opened ≤ OPEN_BUDGET positions.card ∧ checked ≤ CHECK_BUDGET positions.card) oracle message positions)
  exact observed.trans (cap_program_honest_budgets oracle message positions)
end CommitGolfCandidate
