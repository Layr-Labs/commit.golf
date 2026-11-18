import CommitGolfCandidate.CapBinding
import CommitGolfCandidate.CapPositions

/-! Connect lower authentication records and shared cap witnesses to the
collision extractor. A record climbs from its group digest through the lower
siblings to its cap leaf, every node being the compression reply with its top
two bytes cleared. The extractor returns equal group digests or two different
replayed compression inputs whose replies agree on their low 240 bits. -/
namespace CommitGolfCandidate
open CommitGolf

theorem cap_opening_inputs_subset (compress : Compression) (group : Digest)
    (lower upper : List (Bool × Digest)) (capInputs : List (BitVec 512))
    (included : ∀ input ∈ pathInputs compress (climb compress group lower) upper,
      input ∈ capInputs) :
    ∀ input ∈ pathInputs compress group (lower ++ upper),
      input ∈ pathInputs compress group lower ++ capInputs := by
  intro input member
  simp only [cap_path_inputs_append, List.mem_append] at member ⊢
  rcases member with lowerMember | upperMember
  · exact Or.inl lowerMember
  · exact Or.inr (included input upperMember)

/-- Two accepted records at the same original index either have equal group
digests or produce two different inputs, among the selected lower-record inputs
and the paid cap replay inputs, whose replies agree on their low 240 bits. The
lower directions are equal (both are fixed by the index) and the cap
directions are those of the path to the index's cap leaf. -/
theorem cap_record_collision (oracle : Oracle) (index : Index)
    (leftView rightView : CapView 8) (leftProof rightProof leftRest rightRest : List Digest)
    (root leftGroup rightGroup : Digest) (leftLower rightLower : List (Bool × Digest))
    (sameDirections : leftLower.map Prod.fst = rightLower.map Prod.fst)
    (leftAccepted : capDecode (s6Compress oracle.compression) leftView leftProof =
      some (root, leftRest))
    (rightAccepted : capDecode (s6Compress oracle.compression) rightView rightProof =
      some (root, rightRest))
    (leftKnown : capLeafValue leftView (capRequestedPath index) =
      some (climb (s6Compress oracle.compression) leftGroup leftLower))
    (rightKnown : capLeafValue rightView (capRequestedPath index) =
      some (climb (s6Compress oracle.compression) rightGroup rightLower)) :
    ∃ leftCapInputs rightCapInputs : List (BitVec 512),
      oracle.run (capReplayQ leftView leftProof) =
        pure (some (root, leftRest, leftCapInputs), leftCapInputs.length) ∧
      oracle.run (capReplayQ rightView rightProof) =
        pure (some (root, rightRest, rightCapInputs), rightCapInputs.length) ∧
      (leftGroup = rightGroup ∨
        ∃ input ∈ pathInputs (s6Compress oracle.compression) leftGroup leftLower ++ leftCapInputs,
          ∃ input' ∈ pathInputs (s6Compress oracle.compression) rightGroup rightLower ++
              rightCapInputs,
            input ≠ input' ∧
              s6Compress oracle.compression input = s6Compress oracle.compression input') := by
  obtain ⟨leftCapInputs, leftRun, leftUpper, _, leftBits, leftRoot, leftIncluded⟩ :=
    cap_accepted_replay_path oracle leftView leftProof leftRest root leftAccepted
      (capRequestedPath index) _ leftKnown
  obtain ⟨rightCapInputs, rightRun, rightUpper, _, rightBits, rightRoot, rightIncluded⟩ :=
    cap_accepted_replay_path oracle rightView rightProof rightRest root rightAccepted
      (capRequestedPath index) _ rightKnown
  have directions : (leftLower ++ leftUpper).map Prod.fst =
      (rightLower ++ rightUpper).map Prod.fst := by
    simp only [List.map_append, sameDirections, leftBits, rightBits]
  have roots : climb (s6Compress oracle.compression) leftGroup (leftLower ++ leftUpper) =
      climb (s6Compress oracle.compression) rightGroup (rightLower ++ rightUpper) := by
    simpa only [climb, List.foldl_append] using leftRoot.trans rightRoot.symm
  refine ⟨leftCapInputs, rightCapInputs, leftRun, rightRun, ?_⟩
  by_cases groups : leftGroup = rightGroup
  · exact Or.inl groups
  · obtain ⟨input, leftMember, input', rightMember, collision⟩ :=
      collision_of_climb_eq (s6Compress oracle.compression) leftGroup rightGroup
        (leftLower ++ leftUpper) (rightLower ++ rightUpper) directions groups roots
    exact Or.inr ⟨input,
      cap_opening_inputs_subset _ _ _ _ _ leftIncluded input leftMember, input',
      cap_opening_inputs_subset _ _ _ _ _ rightIncluded input' rightMember, collision⟩
end CommitGolfCandidate
