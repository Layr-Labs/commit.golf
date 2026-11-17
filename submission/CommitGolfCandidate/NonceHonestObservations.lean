import CommitGolfCandidate.NonceHonestProof
import CommitGolfCandidate.CapCompleteness
import CommitGolfCandidate.CapBudgets

namespace CommitGolfCandidate
open CommitGolf OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 600000

theorem nonce_honest_observe {α : Type} (observe : Bool → Nat → Nat → Nat → α)
    (oracle : Oracle) (message : Message) (positions : Positions) :
    (fun result : Scheme.HonestResult => observe result.accepted result.commitCalls result.openCalls result.checkCalls) <$>
      nonceCompressedProgram.scheme.honest oracle message positions=
    (fun result : Scheme.HonestResult => observe result.accepted result.commitCalls result.openCalls result.checkCalls) <$>
      capProgram.scheme.honest oracle message positions := by
  unfold Scheme.honest
  simp only [map_bind,map_pure,nonce_compressed_commit_same]
  apply bind_congr
  rintro ⟨⟨root,trapdoor⟩,calls⟩
  erw [nonce_compressed_opening_scheme,nonce_old_scheme_opening,map_pure,
    oracle_run_pure,oracle_run_pure]
  simp only [pure_bind,noncePostprocess]
  erw [nonce_honest_check_eq]

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
