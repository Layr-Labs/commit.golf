import CommitGolfCandidate.C3PermWitnessBound

/-! The complete replay bound for the 3c1p leaf: the leader's compression bound for every fixed
permutation (`3q/(4·2^120)`) plus the cross-oracle event (`q/2^122`). -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp

abbrev C3ReplayBound :=
  ∀ (program : OracleComp World Unit) (q calls : Nat),
    1 ≤ q → q ≤ 2 ^ 120 → calls ≤ q + 2 ^ 31 → PublicQueryBound (recordRows program) calls →
    Pr{let result ← (Oracle.sample >>= fun oracle => fixedOracleRun oracle (recordRows program))}[
      C3ReplayEvidence result.2] ≤ (q : ENNReal) / 2 ^ 120

theorem c3_replay_bound : C3ReplayBound := by
  intro program q calls positive small replayed bounded
  unfold C3ReplayEvidence
  refine (prEvent_or_le _ _ _).trans ((add_le_add ?_ ?_).trans_eq (event_budget_sum q))
  · have exchanged := EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm) (fun compress perm =>
        fixedOracleRun ⟨compress, perm⟩ (recordRows program)))
    simp only [Oracle.sample, bind_assoc, pure_bind]
    rw [exchanged.prEvent_eq (fun result => CompressionWitness result.2)]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ =>
      fixed_permutation_projected_bound p program q calls positive small replayed bounded
  · exact c3_perm_witness_bound program q calls positive small replayed bounded

end TwoPermutationPrototype.Sampling
