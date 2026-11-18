import CommitGolfCandidate.K3OpenReply

/-!
# Group replies in the trapdoor: the commit side and the opener use the same slices

The commit leaves the reply of quartet group `g` at word `Grouped.groupReplyWord g` (`B_g + 168` for an
even group, over its `d3`; `B_{g-1} - 32` for an odd group, whose block sits 200 bytes below the even one).
The opener reads it from the trapdoor at byte `groupReplyOffset g`: `32 L + 1024 g + 168` (even) and
`32 L + 1024 (g - 1) - 32` (odd). Both name the same 200 bytes, so the commit's reply facts hold for the
opener's view of the trapdoor.
-/

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.RV64

/-- The opener's offset is the commit's (`8 * groupReplyWord g - trapdoorBase`). -/
theorem group_offset_eq (g : Nat) : groupReplyOffset g=Grouped.groupReplyOffset g := by
  unfold groupReplyOffset Grouped.groupReplyOffset Grouped.groupReplyWord Grouped.unitBase Grouped.unitFirst Grouped.unitStride
    Grouped.cellFirst Grouped.trapdoorBase LENGTH LOG_LENGTH
  split <;> omega

/-- The commit's trapdoor slice of group `g` is the opener's. -/
theorem group_reply_eq {n : Nat} (td : BitVec n) (g : Nat) : Grouped.trapdoorGroupReply td g=groupReply td g := by
  unfold Grouped.trapdoorGroupReply groupReply
  rw [group_offset_eq]

/-- The commit's reply clause (`physical_results`, slice form) in the opener's form (`opened_proof`'s `replies`). -/
theorem replies_of_trapdoor {n : Nat} (td : BitVec n) (R : Nat → BitVec 1600)
    (h : ∀ g, g<4194304 → Grouped.trapdoorGroupReply td g=R g) : ∀ g<4194304, groupReply td g=R g :=
  fun g hg => (group_reply_eq td g).symm.trans (h g hg)

end TwoPermutationPrototype.GroupedOpening
