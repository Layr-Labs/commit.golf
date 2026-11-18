import CommitGolfCandidate.OverlapInputs
import CommitGolfCandidate.TwoPermutationBindingLeaf

namespace TwoPermutationPrototype.Overlap
open CommitGolf TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

def firstRow (perm : Block → Block) (m : Words 32) : Row :=
  let x := packBuffer (Overlap.firstInput m)
  (x,perm x)

def secondRow (perm : Block → Block) (i : Index) (s : Words 2) (m : Words 32) (a : Block) : Row :=
  let w := packBuffer (Overlap.secondInput i.val s (replyWords a) m)
  (w,perm w)

end TwoPermutationPrototype.Overlap
