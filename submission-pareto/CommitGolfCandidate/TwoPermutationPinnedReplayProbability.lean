import CommitGolfCandidate.TwoPermutationPinnedLeafWidth

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp OracleComp.DeferredSampling
set_option maxRecDepth 8192
set_option exponentiation.threshold 2100

theorem pinned_replay_bound_of_layout (layout : PeerLeafLayout) : PinnedReplayBound := by
  intro program q calls positive small replayed bounded
  unfold PinnedReplayEvidence
  refine (prEvent_or_le _ _ _).trans ((add_le_add ?_ ?_).trans_eq (event_budget_sum q))
  · have exchanged := EvalDistEq.of_evalDist_eq
      (distribution_bind_comm ($ᵗ Compression) ($ᵗ Perm) (fun compress perm =>
        fixedOracleRun ⟨compress,perm⟩ (recordRows program)))
    simp only [Oracle.sample,bind_assoc,pure_bind]
    rw [exchanged.prEvent_eq (fun result => CompressionWitness result.2)]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun p _ =>
      fixed_permutation_projected_bound p program q calls positive small replayed bounded
  · simp only [Oracle.sample,bind_assoc,pure_bind]
    exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun compress _ =>
      pinned_leaf_bound_width 244 (by decide) (by decide) layout compress program q calls positive small replayed bounded

end TwoPermutationPrototype.Sampling
