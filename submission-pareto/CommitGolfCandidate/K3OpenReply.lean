import CommitGolfCandidate.K3CUUnits

/-!
# Group replies in the trapdoor, opener side

The odd quartet block sits 200 bytes below the even block of its octet, so the commit leaves the reply of
quartet group `g` at trapdoor byte `32 L + 1024 g + 168` (reply_E, even `g`) and `32 L + 1024 (g - 1) - 32`
(reply_O, odd `g`). `K3GRBridge` shows these are the commit's slices.
-/

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.RV64

/-- Trapdoor byte offset of group `g`'s reply: reply_E of an even group at `B_g+168`, reply_O of an odd group at
`B_{g-1}-32`. -/
def groupReplyOffset (g : Nat) : Nat := if g%2=0 then 32*LENGTH+1024*g+168 else 32*LENGTH+1024*(g-1)-32
/-- The reply of group `g` as stored in a trapdoor. -/
def groupReply {n : Nat} (td : BitVec n) (g : Nat) : BitVec 1600 := td.extractLsb' (8*groupReplyOffset g) 1600

end TwoPermutationPrototype.GroupedOpening
