import CommitGolfCandidate.Leaf238ReplayProbability

namespace TwoPermutationPrototype.Sampling

theorem pinned_replay_bound_of_layout (layout : PeerLeafLayout) : PinnedReplayBound := by
  intro program q calls positive _small replayed bounded
  simpa only [PinnedReplayEvidence, PinnedLeafWitness, PinnedLeafWitnessW] using
    joint_replay_bound_238_of_layout layout program q calls positive replayed bounded

end TwoPermutationPrototype.Sampling
