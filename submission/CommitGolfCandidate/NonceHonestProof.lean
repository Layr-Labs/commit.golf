import CommitGolfCandidate.NonceCheckScheme
import CommitGolfCandidate.S6HonestCanonical
import CommitGolfCandidate.HidingMachine
import CommitGolfCandidate.CapCommitBridge

/-! Honest proof expansion recovers exactly the cap-level opening, including the
empty-position case. The packed proof of a committed trapdoor expands back to the
cap-level proof because that proof is canonical: tagged salts and truncated nodes. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

def nonceOldSchemeProof (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) : Proof :=
  if positions.card=0 then [] else capOpenLoadedBytes trapdoor positions

theorem nonce_old_scheme_opening (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions) :
    capProgram.scheme.opening trapdoor positions=pure (nonceOldSchemeProof trapdoor positions) := by
  unfold nonceOldSchemeProof
  split
  · exact cap_open_empty_scheme_bytes trapdoor positions ‹_›
  · exact cap_open_nonempty_scheme_bytes trapdoor positions (by omega)

theorem nonce_delivered_scheme_opening (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    nonceCompressedProgram.scheme.opening trapdoor positions=
      pure (s6Pack positions.card (nonceOldSchemeProof trapdoor positions)) := by
  rw [nonce_compressed_opening_scheme, nonce_old_scheme_opening, map_pure]
  rfl

theorem nonce_old_scheme_capacity (trapdoor : BitVec (8*capProgram.sizes.trapdoor))
    (positions : Positions) :
    (nonceOldSchemeProof trapdoor positions).length ≤ capProgram.sizes.proof := by
  unfold nonceOldSchemeProof
  split
  · exact Nat.zero_le _
  · exact cap_open_loaded_bytes_capacity trapdoor positions

theorem nonce_honest_check_eq (trapdoor : BitVec (8*capProgram.sizes.trapdoor)) (positions : Positions)
    (root : Commitment) (values : Values positions)
    (canonical : S6Canonical positions (nonceOldSchemeProof trapdoor positions)) :
    nonceCompressedProgram.scheme.check root positions values
      (s6Pack positions.card (nonceOldSchemeProof trapdoor positions))=
      capProgram.scheme.check root positions values (nonceOldSchemeProof trapdoor positions) := by
  let input : CheckInput :=
    ⟨root,positions,values,s6Pack positions.card (nonceOldSchemeProof trapdoor positions)⟩
  obtain ⟨valid,expanded⟩ := nonce_check_valid_of_expand input _
    (s6_expand_pack positions _ canonical) (nonce_old_scheme_capacity trapdoor positions)
  have checkEq := nonce_check_scheme_valid input valid
  rw [expanded] at checkEq
  exact checkEq

/-- Every trapdoor the commitment can return gives a canonical cap-level proof. -/
theorem nonce_honest_commit_canonical (oracle : Oracle) (message : Message)
    (result : (Commitment × capProgram.scheme.Trapdoor) × Nat)
    (reachable : result ∈ support (oracle.run (capProgram.scheme.commit message)))
    (positions : Positions) :
    S6Canonical positions (nonceOldSchemeProof result.1.2 positions) := by
  change result ∈ support (oracle.run
    (capProgram.readCommit <$> (capProgram.run .commit message : OracleComp World Execution)))
    at reachable
  erw [oracle_run_map] at reachable
  simp only [support_map] at reachable
  obtain ⟨execution,reached,rfl⟩ := reachable
  have correct := cap_commit_matches oracle message execution reached
  unfold nonceOldSchemeProof
  split
  · rename_i empty
    have none : positions = ∅ := Finset.card_eq_zero.mp empty
    subst none
    unfold S6Canonical
    simp [S6RecordsCanonical, S6NodesCanonical]
  · exact cap_honest_loaded_canonical oracle message execution.1.state correct positions

end CommitGolfCandidate
