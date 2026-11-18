import CommitGolfCandidate.OverlapCommitHandoff
import CommitGolfCandidate.PlbHidingBridge

namespace TwoPermutationPrototype.Overlap
open CommitGolf TwoPermutationPrototype.Sampling

/-- The commit machine's digest tape is the one used by the binding and hiding reductions. -/
theorem digest_tape_matches (o : Oracle) (m : Message) (s : CompleteSaltTape) :
    leafDigests o m s = plbLeafDigests (BiPermutation.equiv Block o.permutation) m s := rfl

noncomputable def plbCommitted : Opening.PlbCommitTranscript program where
  trapdoorOf := committed.trapdoorOf
  distribution := committed.distribution
  nonce := committed.nonce
  heap := committed.heap

end TwoPermutationPrototype.Overlap
