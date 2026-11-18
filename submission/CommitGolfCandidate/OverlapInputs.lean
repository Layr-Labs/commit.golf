import CommitGolfCandidate.TwoPermutationLeaf

namespace TwoPermutationPrototype.Overlap

/-- One zero word followed by the first 24 message words. -/
def firstInput (message : Words 32) : Words 25 := fun j =>
  if h0 : j.val = 0 then 0 else message ⟨j.val-1, by have := j.isLt; omega⟩

/-- The position tag, the last four reply words, two salt words, and the last 18 message words. -/
def secondInput (index : Nat) (nonce : Words 2) (reply : Words 25) (message : Words 32) : Words 25 := fun j =>
  if h0 : j.val = 0 then secondTag index
  else if h5 : j.val < 5 then reply ⟨j.val+20, by omega⟩
  else if h7 : j.val < 7 then nonce ⟨j.val-5, by omega⟩
  else message ⟨j.val+7, by have := j.isLt; omega⟩

def digest (perm : Permutation) (index : Nat) (nonce : Words 2) (message : Words 32) : Words 4 :=
  lowDigest (perm (secondInput index nonce (perm (firstInput message)) message))

end TwoPermutationPrototype.Overlap
