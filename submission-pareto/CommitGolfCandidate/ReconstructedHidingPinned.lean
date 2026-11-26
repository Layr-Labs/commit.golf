import CommitGolfCandidate.ReconstructedHidingGuesses
import CommitGolfCandidate.TaggedPinnedBitLayout

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf TwoPermutationPrototype.Sampling TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

theorem mask_widen (s : Salt) : maskSalt (s.setWidth 128) = s.setWidth 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases small : i < 120
  · have mask : saltMask.getLsbD i = true := by
      rw [saltMask,BitVec.getLsbD_ofNat,Nat.testBit_two_pow_sub_one]
      simp only [decide_eq_true_eq,Bool.and_eq_true]
      omega
    simp only [maskSalt,BitVec.getLsbD_and,mask,Bool.and_true]
  · have dead : s.getLsbD i = false := BitVec.getLsbD_of_ge s i (by omega)
    simp only [maskSalt,BitVec.getLsbD_and,BitVec.getLsbD_setWidth,dead,Bool.and_false,Bool.false_and]

theorem semantic_second_input (m : Message) (i : Index) (reply : Reply) (s : Salt) :
    packBuffer (pinnedSecondInput i (saltWords (maskSalt (s.setWidth 128))) (replyWords reply)
      (messageWords m i)) = leafAddress i (m i) reply s := by
  rw [mask_widen s]
  refine (pinned_pack_second_input m i reply (s.setWidth 128)).trans ?_
  have widen : s.setWidth 128 = 0#8 ++ s := BitVec.setWidth_eq_append (by decide)
  rw [widen]
  simp only [leafAddress,tag,pinnedPositionTag,BitVec.append_assoc,BitVec.cast_eq]
  exact congrArg (fun z : BitVec 192 => (m i).extractLsb' 1344 704 ++ (reply.extractLsb' 896 704 ++ z))
    (BitVec.append_assoc (x₁ := 0#8) (x₂ := s) (x₃ := tag i))

theorem semantic_tag_hit {I : Type} (pos : I → Position) (i : I) (m : Message)
    (first : I → Reply) (s : I → Salt) :
    tagHit pos (packBuffer (pinnedSecondInput (pos i) (saltWords (maskSalt ((s i).setWidth 128)))
      (replyWords (first i)) (messageWords m (pos i)))) s := by
  exact (congrArg (fun y => tagHit pos y s) (semantic_second_input m (pos i) (first i) (s i))).mpr
    (leaf_address_hit pos i (m (pos i)) (first i) s)

theorem semantic_first_input (m : Message) (i : Index) :
    packBuffer (pinnedFirstInput (messageWords m i)) = (m i).extractLsb' 0 1600 :=
  pinned_pack_first_input m i

end CommitGolfCandidate.Reconstruction.HidingTape
