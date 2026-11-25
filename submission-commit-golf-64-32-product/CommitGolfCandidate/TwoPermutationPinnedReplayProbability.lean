import CommitGolfCandidate.K1HideLeafBinding

/-! The pinned replay bound from a leaf layout. With the K1 leaf the per-kind collision analysis
lives in `K1HideLeafBinding.lean`; this module keeps the record's name for the step from a
`PeerLeafLayout` to the `PinnedReplayBound`. -/
namespace TwoPermutationPrototype.Sampling

theorem pinned_replay_bound_of_layout (layout : PeerLeafLayout) : PinnedReplayBound :=
  pinned_replay_bound_of_k1_layout layout

end TwoPermutationPrototype.Sampling
