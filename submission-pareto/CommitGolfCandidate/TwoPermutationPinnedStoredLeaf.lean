import CommitGolfCandidate.TwoPermutationPinnedRecorded
import CommitGolfCandidate.TwoPermutationCheckerPaths

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation TwoPermutationPrototype.RV64
set_option maxRecDepth 8192

structure PeerLeafLayout where
  salt : Index → BitVec 128 → BitVec 256
  first : ∀ (index : Index) (value : CommitGolf.Entry),
    packBuffer (pinnedFirstInput (entryWords value)) = s3First value
  second : ∀ (index : Index) (value : CommitGolf.Entry) (nonce : BitVec 128) (reply : Block),
    packBuffer (pinnedSecondInput index (saltWords nonce) (replyWords reply) (entryWords value)) =
      s3Second (salt index nonce) reply value

end TwoPermutationPrototype.Sampling
