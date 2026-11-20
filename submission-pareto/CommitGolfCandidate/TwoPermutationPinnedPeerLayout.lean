import CommitGolfCandidate.K1HideLeafBinding

/-! The salt-first peer layout of the K1 leaf: rank ≠ 0 leaves are the stage-3 pinned two-call hash
`s3First`/`s3Second` with peer salt `0^64 ‖ tag ‖ salt` (`K1HideLeafBinding.lean`). The record's
names are kept for the salt-first case. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.RV64

abbrev pinnedPeerSalt := k1PeerSalt

theorem pinned_first_peer (index : Index) (value : Entry) (kind : isAHead index = false) :
    packBuffer (pinnedFirstInput index (entryWords value)) = s3First value :=
  k1_first_sf index value kind

theorem pinned_second_peer (index : Index) (value : Entry) (salt : BitVec 128) (reply : Block)
    (kind : isAHead index = false) :
    packBuffer (pinnedSecondInput index (saltWords salt) (replyWords reply) (entryWords value)) =
      s3Second (pinnedPeerSalt index salt) reply value :=
  k1_second_sf index value salt reply kind

end TwoPermutationPrototype.Sampling
