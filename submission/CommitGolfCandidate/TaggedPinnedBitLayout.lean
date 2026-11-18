import CommitGolfCandidate.TaggedPinnedModel

namespace TwoPermutationPrototype.Sampling
open CommitGolf TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

private theorem pinned_block_eq_of_words (a b : BitVec 1600)
    (words : ∀ j : Fin 25, a.extractLsb' (64 * j.val) 64 = b.extractLsb' (64 * j.val) 64) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  have same := congrArg (fun chunk : BitVec 64 => chunk.getLsbD (bit % 64)) (words ⟨bit / 64, by omega⟩)
  have inner : bit % 64 < 64 := by omega
  have address : 64 * (bit / 64) + bit % 64 = bit := by omega
  simpa [inner, address] using same

private theorem pinned_nested_slice {size : Nat} (word : BitVec size) {outer width start len : Nat}
    (room : start + len ≤ width) :
    (word.extractLsb' outer width).extractLsb' start len = word.extractLsb' (outer + start) len := by
  apply BitVec.eq_of_getLsbD_eq
  intro i inside
  have mid : start + i < width := by omega
  simp [mid, inside, Nat.add_assoc]

/-- The first window of a salt-first leaf is message bytes `0..200`. -/
theorem pinned_pack_first_input_sf (message : Message) (i : Index) (kind : isAHead i = false) :
    packBuffer (pinnedFirstInput i (messageWords message i)) = (message i).extractLsb' 0 1600 := by
  apply pinned_block_eq_of_words
  intro j
  rw [packed_word, pinned_nested_slice _ (by have := j.isLt; omega : 64 * j.val + 64 ≤ 1600)]
  simp only [pinnedFirstInput, kind, Bool.false_eq_true, ite_false, messageWords, Nat.zero_add]

/-- The first window of an A leaf is message bytes `56..256`. -/
theorem pinned_pack_first_input_a (message : Message) (i : Index) (kind : isAHead i = true) :
    packBuffer (pinnedFirstInput i (messageWords message i)) = (message i).extractLsb' 448 1600 := by
  apply pinned_block_eq_of_words
  intro j
  rw [packed_word, pinned_nested_slice _ (by have := j.isLt; omega : 64 * j.val + 64 ≤ 1600)]
  simp only [pinnedFirstInput, kind, ite_true, messageWords]
  congr 1
  omega

/-- The first window, both kinds: message bits from `448` (A leaf) or `0` (salt-first leaf). -/
theorem pinned_pack_first_input (message : Message) (i : Index) :
    packBuffer (pinnedFirstInput i (messageWords message i)) =
      (message i).extractLsb' (if isAHead i then 448 else 0) 1600 := by
  cases kind : isAHead i
  · simpa only [Bool.false_eq_true, ite_false] using pinned_pack_first_input_sf message i kind
  · simpa only [ite_true] using pinned_pack_first_input_a message i kind

/-- Salt-first second window: `salt ‖ tag ‖ reply[112..200) ‖ v[168..256)`, low bits first. -/
theorem pinned_pack_second_input_sf (message : Message) (index : Index) (reply : Block) (nonce : BitVec 128)
    (kind : isAHead index = false) :
    packBuffer (pinnedSecondInput index (saltWords nonce) (replyWords reply) (messageWords message index)) =
      (message index).extractLsb' 1344 704 ++ (reply.extractLsb' 896 704 ++ (pinnedPositionTag index ++ nonce)) := by
  apply pinned_block_eq_of_words
  intro j
  rw [packed_word]
  let phase := pinnedPositionTag index ++ nonce
  let chain := reply.extractLsb' 896 704
  let values := (message index).extractLsb' 1344 704
  change _ = (values ++ (chain ++ phase)).extractLsb' (64 * j.val) 64
  have fits := j.isLt
  by_cases nonceWord : j.val < 2
  · have two : j.val ≠ 2 := by omega
    simp only [pinnedSecondInput, kind, Bool.false_eq_true, ite_false, two, nonceWord, dite_true, saltWords]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 896),
      BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 192),
      BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 128)]
  · by_cases tagWord : j.val = 2
    · simp only [pinnedSecondInput, kind, Bool.false_eq_true, ite_false, tagWord, ite_true]
      rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * 2 + 64 ≤ 896),
        BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * 2 + 64 ≤ 192)]
      exact BitVec.extractLsb'_append_eq_left.symm
    · by_cases chainWord : j.val < 14
      · simp only [pinnedSecondInput, kind, Bool.false_eq_true, ite_false, tagWord, nonceWord, chainWord,
          dite_false, dite_true, replyWords]
        rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 896),
          BitVec.extractLsb'_append_eq_of_le (by omega : 192 ≤ 64 * j.val)]
        change _ = (reply.extractLsb' 896 704).extractLsb' (64 * j.val - 192) 64
        rw [pinned_nested_slice _ (by omega : 64 * j.val - 192 + 64 ≤ 704)]
        congr 1
        omega
      · simp only [pinnedSecondInput, kind, Bool.false_eq_true, ite_false, tagWord, nonceWord, chainWord,
          dite_false, messageWords]
        rw [BitVec.extractLsb'_append_eq_of_le (by omega : 896 ≤ 64 * j.val)]
        change _ = ((message index).extractLsb' 1344 704).extractLsb' (64 * j.val - 896) 64
        rw [pinned_nested_slice _ (by omega : 64 * j.val - 896 + 64 ≤ 704)]
        congr 1
        omega

/-- A-leaf second window: `reply[144..160) ‖ tag ‖ reply[168..200) ‖ v[0..128) ‖ salt`, low bits first. -/
theorem pinned_pack_second_input_a (message : Message) (index : Index) (reply : Block) (nonce : BitVec 128)
    (kind : isAHead index = true) :
    packBuffer (pinnedSecondInput index (saltWords nonce) (replyWords reply) (messageWords message index)) =
      nonce ++ ((message index).extractLsb' 0 1024 ++
        (reply.extractLsb' 1344 256 ++ (pinnedPositionTag index ++ reply.extractLsb' 1152 128))) := by
  apply pinned_block_eq_of_words
  intro j
  rw [packed_word]
  let low := reply.extractLsb' 1152 128
  let phase := pinnedPositionTag index ++ low
  let chain := reply.extractLsb' 1344 256 ++ phase
  let values := (message index).extractLsb' 0 1024 ++ chain
  change _ = (nonce ++ values).extractLsb' (64 * j.val) 64
  have fits := j.isLt
  by_cases lowWord : j.val < 2
  · have two : j.val ≠ 2 := by omega
    have seven : j.val < 7 := by omega
    simp only [pinnedSecondInput, kind, ite_true, two, ite_false, seven, dite_true, replyWords]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 1472),
      BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 448),
      BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 192),
      BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 128)]
    change _ = (reply.extractLsb' 1152 128).extractLsb' (64 * j.val) 64
    rw [pinned_nested_slice _ (by omega : 64 * j.val + 64 ≤ 128)]
    congr 1
    omega
  · by_cases tagWord : j.val = 2
    · simp only [pinnedSecondInput, kind, ite_true, tagWord]
      rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * 2 + 64 ≤ 1472),
        BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * 2 + 64 ≤ 448),
        BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * 2 + 64 ≤ 192)]
      exact BitVec.extractLsb'_append_eq_left.symm
    · by_cases chainWord : j.val < 7
      · simp only [pinnedSecondInput, kind, ite_true, tagWord, ite_false, chainWord, dite_true, replyWords]
        rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 1472),
          BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 448),
          BitVec.extractLsb'_append_eq_of_le (by omega : 192 ≤ 64 * j.val)]
        change _ = (reply.extractLsb' 1344 256).extractLsb' (64 * j.val - 192) 64
        rw [pinned_nested_slice _ (by omega : 64 * j.val - 192 + 64 ≤ 256)]
        congr 1
        omega
      · by_cases messageWord : j.val < 23
        · simp only [pinnedSecondInput, kind, ite_true, tagWord, ite_false, chainWord, messageWord,
            dite_false, dite_true, messageWords]
          rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 1472),
            BitVec.extractLsb'_append_eq_of_le (by omega : 448 ≤ 64 * j.val)]
          change _ = ((message index).extractLsb' 0 1024).extractLsb' (64 * j.val - 448) 64
          rw [pinned_nested_slice _ (by omega : 64 * j.val - 448 + 64 ≤ 1024)]
          congr 1
          omega
        · simp only [pinnedSecondInput, kind, ite_true, tagWord, ite_false, chainWord, messageWord,
            dite_false, saltWords]
          rw [BitVec.extractLsb'_append_eq_of_le (by omega : 1472 ≤ 64 * j.val)]
          congr 1
          omega

end TwoPermutationPrototype.Sampling
