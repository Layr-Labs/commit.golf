import CommitGolfCandidate.K3CBLeaf
import CommitGolfCandidate.LinkedSaltLayout
import CommitGolfCandidate.TaggedPinnedModel
import CommitGolfCandidate.TwoPermutationHidingTwoStage
import CommitGolfCandidate.QuartetCommitRanges

/-!
# K3-lite body: the values the commit stores

The generator replies follow the final salt schedule `chain` (a keyed restart every 34 heads of a
tile, every other head linked to the previous head's reply); leaf digests use its salts; the
quartet window of group `g` is `0^9 ‖ d0 d1 d2 d3` (`quartetWindow`) and its reply `quartetReply`.
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation.CounterSalt (coord input)
open TwoPermutationPrototype.QuartetCommit (qSource)

/-- Where the group call of quartet `g` writes its reply: over its fourth digest, `B_g + 168` (both parities). -/
def replyWord (g : Nat) := qSource g+21

/-- The final salt schedule: a keyed restart every 34 heads of a tile, every other head linked. -/
abbrev chain := CommitGolfCandidate.Permutation.LinkedSalt.schedule CommitGolfCandidate.Permutation.LinkedSalt.period
/-- The generator reply of the group of `i`. -/
def groupReply (o : Oracle) (k : BitVec 192) (i : Index) : BitVec 1600 :=
  chain.reply (S := CommitGolfCandidate.Permutation.NonceChain.Word1600) o.permutation input k (coord i).1
/-- The salts of the final schedule. -/
noncomputable def chainSalts (o : Oracle) (k : BitVec 192) :=
  CommitGolfCandidate.Permutation.LinkedSalt.salts chain o.permutation k
noncomputable def value (o : Oracle) (k : BitVec 192) (m : Message) (i : Index) :=
  pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) m (chainSalts o k) i
/-- The four words of a digest (definitionally `QuartetCommit.digestWords`). -/
def digestOf (v : BitVec 256) : Words 4 := fun k => v.extractLsb' (64*k.val) 64
def firstOf (o : Oracle) (msg : Message) (i : Index) := (pinnedFirstRow o.permutation i (messageWords msg i)).2
noncomputable def leafVal (o : Oracle) (k : BitVec 192) (msg : Message) (j : Nat) : BitVec 256 :=
  if h : j<LENGTH then value o k msg ⟨j,h⟩ else 0
/-- The record window of quartet `g`: `0^9 ‖ d0 d1 d2 d3`. -/
noncomputable def quartetWindow (o : Oracle) (k : BitVec 192) (msg : Message) (g : Nat) : Words 25 := fun w =>
  if w.val<9 then 0 else digestOf (leafVal o k msg (4*g+(w.val-9)/4)) ⟨(w.val-9)%4,by omega⟩
noncomputable def quartetReply (o : Oracle) (k : BitVec 192) (msg : Message) (g : Nat) :=
  o.permutation (packBuffer (quartetWindow o k msg g))

end TwoPermutationPrototype.Grouped
