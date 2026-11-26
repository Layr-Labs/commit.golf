import CommitGolfCandidate.HidingTree

import CommitGolfCandidate.TruncModel

namespace CommitGolfCandidate.Trunc

open CommitGolf

set_option maxRecDepth 12000

set_option maxHeartbeats 800000

def saltedHeap (compress : Compression) (message : Message) (salt : Index → Salt) :
    Nat → Digest :=
  referenceHeap compress LENGTH fun index =>
    if inside : index < LENGTH then
      leafDigest compress ⟨index, inside⟩ (salt ⟨index, inside⟩) (message ⟨index, inside⟩)
    else 0

def hybridHeap (compress : Compression) (positions : Positions) (message : Message)
    (salt : Index → Salt) (freshInit : Index → Digest) : Nat → Digest :=
  referenceHeap compress LENGTH fun index =>
    if inside : index < LENGTH then
      hybridLeafDigest compress positions message salt freshInit ⟨index, inside⟩
    else 0

end CommitGolfCandidate.Trunc
