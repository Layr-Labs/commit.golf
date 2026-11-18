import CommitGolfCandidate.TwoPermutationPinnedPeerLayout
import CommitGolfCandidate.TwoPermutationPinnedReplayProbability

namespace TwoPermutationPrototype.Sampling

/-- The pinned replay bound of the K1 leaf (both leaf kinds; `K1HideLeafBinding.lean`). -/
theorem pinned_replay_bound : PinnedReplayBound :=
  pinned_replay_bound_of_layout k1_peer_leaf_layout

end TwoPermutationPrototype.Sampling
