import CommitGolfCandidate.NonceHonestProof
import CommitGolfCandidate.CapCompleteness
import CommitGolfCandidate.CapBudgets

/-! Acceptance and each stage's public query count agree with the original
honest game. Proof bytes change, and are bounded separately from this view. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 600000

private def observeOpening {α : Type} (scheme : Scheme) (observe : Bool → Nat → Nat → Nat → α)
    (oracle : Oracle) (message : Message) (positions : Positions)
    (root : Commitment) (trapdoor : scheme.Trapdoor) (commitCalls : Nat) : ProbComp α := do
  let (proof, openCalls) ← oracle.run (scheme.opening trapdoor positions)
  let (accepted, checkCalls) := oracle.eval (scheme.check root positions (message.restrict positions) proof)
  return observe accepted commitCalls openCalls checkCalls

private theorem observeOpeningSame {α : Type} (observe : Bool → Nat → Nat → Nat → α)
    (oracle : Oracle) (message : Message) (positions : Positions)
    (root : Commitment) (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (commitCalls : Nat) :
    observeOpening nonceCompressedProgram.scheme observe oracle message positions root trapdoor commitCalls =
      observeOpening capProgram.scheme observe oracle message positions root trapdoor commitCalls := by
  unfold observeOpening
  rw [nonce_compressed_opening_scheme trapdoor positions,
    nonce_old_scheme_opening trapdoor positions]
  simp only [map_pure,oracle_run_pure,pure_bind,noncePostprocess]
  rw [nonce_honest_check_eq trapdoor positions root (message.restrict positions)]

private theorem observeCommitment {Trapdoor α : Type}
    (commit : ProbComp ((Commitment × Trapdoor) × Nat))
    (left right : Commitment → Trapdoor → Nat → ProbComp α)
    (same : ∀ root trapdoor calls, left root trapdoor calls = right root trapdoor calls) :
    (do let ((root, trapdoor), calls) ← commit
        left root trapdoor calls) =
    (do let ((root, trapdoor), calls) ← commit
        right root trapdoor calls) := by
  apply bind_congr
  rintro ⟨⟨root, trapdoor⟩, calls⟩
  exact same root trapdoor calls

theorem nonce_honest_observe {α : Type} (observe : Bool → Nat → Nat → Nat → α)
    (oracle : Oracle) (message : Message) (positions : Positions) :
    (fun result : Scheme.HonestResult => observe result.accepted result.commitCalls result.openCalls result.checkCalls) <$>
      nonceCompressedProgram.scheme.honest oracle message positions=
    (fun result : Scheme.HonestResult => observe result.accepted result.commitCalls result.openCalls result.checkCalls) <$>
      capProgram.scheme.honest oracle message positions := by
  unfold Scheme.honest
  simp only [map_bind,map_pure,nonce_compressed_commit_same]
  exact observeCommitment (Trapdoor := BitVec (8*capProgram.sizes.trapdoor))
    (oracle.run (capProgram.scheme.commit message))
    (observeOpening nonceCompressedProgram.scheme observe oracle message positions)
    (observeOpening capProgram.scheme observe oracle message positions)
    (observeOpeningSame observe oracle message positions)

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
