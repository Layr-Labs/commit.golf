import CommitGolfCandidate.TwoPermutationHidingEager

/-!
# The K1 leaf model: paired in-place salts (P2H)

Each 11-leaf salt group of a 4096-leaf tile (372 groups of eleven, one of four) starts with an
A leaf (rank 0) followed by salt-first leaves (ranks 1..10; rank 1 is the C leaf whose salt the
generator reply delivers in place, ranks 2..10 copy their salts from the same reply).

* Salt-first leaf (rank ≠ 0), base `L = 4096 + 256 i`: the first call is `π (v[0..200))`, and the
  second-call window `[L+56, L+256)` is `salt (2 words) ‖ tag ‖ reply[112..200) ‖ v[168..256)`,
  tag `L + 56 = 4152 + 256 i`.
* A leaf (rank 0), base `B = 4096 + 256 i`: the first call is `π (v[56..256))` with its reply at
  `[B-200, B)`, and the window `[B-56, B+144)` is
  `reply[144..160) ‖ tag ‖ reply[168..200) ‖ v[0..128) ‖ salt`, tag `B - 56 = 4040 + 256 i`.

Every second-call window has its tag in word 2, and tags of distinct positions differ (they are
`56` or `200` modulo `256`), so second-call inputs of distinct positions never coincide.
The digest is bytes 0..32 of the second reply.
-/

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

/-- Rank 0 of an 11-leaf salt group inside a 4096-leaf tile: the mirrored A leaf. -/
def isAHead (index : Index) : Bool := (index.val % 4096) % 11 == 0

def pinnedPositionTag (index : Index) : BitVec 64 :=
  BitVec.ofNat 64 (if isAHead index then 4040 + 256 * index.val else 4152 + 256 * index.val)

def pinnedFirstInput (index : Index) (message : Words 32) : Words 25 := fun i =>
  if isAHead index then message ⟨i.val + 7, by omega⟩ else message ⟨i.val, by omega⟩

def pinnedSecondInput (index : Index) (nonce : Words 2) (firstReply : Words 25)
    (message : Words 32) : Words 25 := fun i =>
  if isAHead index then
    if i.val = 2 then pinnedPositionTag index
    else if h : i.val < 7 then firstReply ⟨i.val + 18, by omega⟩
    else if h : i.val < 23 then message ⟨i.val - 7, by omega⟩
    else nonce ⟨i.val - 23, by omega⟩
  else
    if i.val = 2 then pinnedPositionTag index
    else if h : i.val < 2 then nonce ⟨i.val, h⟩
    else if h : i.val < 14 then firstReply ⟨i.val + 11, by omega⟩
    else message ⟨i.val + 7, by omega⟩

def pinnedFirstRow (perm : Block → Block) (index : Index) (message : Words 32) : Row :=
  let address := packBuffer (pinnedFirstInput index message)
  (address, perm address)

def pinnedSecondRow (perm : Block → Block) (index : Index) (nonce : Words 2) (firstReply : Block)
    (message : Words 32) : Row :=
  let address := packBuffer (pinnedSecondInput index nonce (replyWords firstReply) message)
  (address, perm address)

def pinnedLeafDigest (perm : Block → Block) (index : Index) (nonce : Words 2)
    (message : Words 32) : BitVec 256 :=
  outputDigest (pinnedSecondRow perm index nonce (pinnedFirstRow perm index message).2 message).2

def pinnedFullLeafDigests (p : BiPermutation Block) (message : Message) (salts : CompleteSaltTape) : DigestTape :=
  fun i => pinnedLeafDigest p.forward i (saltWords (salts i)) (messageWords message i)

private theorem tag_value_lt (index : Index) :
    (if isAHead index then 4040 + 256 * index.val else 4152 + 256 * index.val) < 2^64 := by
  have range : index.val < 2^24 := index.isLt
  split <;> omega

theorem pinned_position_tag_toNat (index : Index) :
    (pinnedPositionTag index).toNat =
      (if isAHead index then 4040 + 256 * index.val else 4152 + 256 * index.val) := by
  unfold pinnedPositionTag
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (tag_value_lt index)]

theorem pinned_position_tag_injective : Function.Injective pinnedPositionTag := by
  intro i j same
  have raw := congrArg BitVec.toNat same
  rw [pinned_position_tag_toNat, pinned_position_tag_toNat] at raw
  apply Fin.ext
  split at raw <;> split at raw <;> omega

theorem pinned_second_tag (index : Index) (nonce : Words 2) (reply : Block) (message : Words 32) :
    (packBuffer (pinnedSecondInput index nonce (replyWords reply) message)).extractLsb' 128 64 =
      pinnedPositionTag index := by
  have word := packed_word (pinnedSecondInput index nonce (replyWords reply) message) (2 : Fin 25)
  have two : (64 * (2 : Fin 25).val) = 128 := rfl
  rw [two] at word
  rw [word]
  unfold pinnedSecondInput
  split <;> rfl

theorem pinned_second_input_nonce_injective (index : Index) (reply : Block) (message : Words 32) :
    Function.Injective (fun nonce : Words 2 => packBuffer (pinnedSecondInput index nonce (replyWords reply) message)) := by
  intro first second same
  have words := packBuffer_injective same
  funext i
  by_cases a : isAHead index
  · let slot : Fin 25 := ⟨i.val + 23, by omega⟩
    have sameWord := congrFun words slot
    have n2 : i.val + 23 ≠ 2 := by omega
    have n7 : ¬ i.val + 23 < 7 := by omega
    have n23 : ¬ i.val + 23 < 23 := by omega
    simpa only [slot, pinnedSecondInput, a, ite_true, n2, ite_false, n7, n23, dite_false,
      Nat.add_sub_cancel, Fin.eta] using sameWord
  · let slot : Fin 25 := ⟨i.val, by omega⟩
    have sameWord := congrFun words slot
    have n2 : i.val ≠ 2 := by omega
    have b : i.val < 2 := i.isLt
    simpa only [slot, pinnedSecondInput, a, Bool.false_eq_true, ite_false, n2, b, dite_true,
      Fin.eta] using sameWord

theorem pinned_second_input_distinct_indices (i j : Index) (r s : Words 2)
    (reply reply' : Block) (message message' : Words 32)
    (same : packBuffer (pinnedSecondInput i r (replyWords reply) message) =
      packBuffer (pinnedSecondInput j s (replyWords reply') message')) : i = j := by
  have tag := congrArg (fun word : Block => word.extractLsb' 128 64) same
  exact pinned_position_tag_injective
    ((pinned_second_tag i r reply message).symm.trans (tag.trans (pinned_second_tag j s reply' message')))

theorem pinned_chaining_preserved (index : Index) (nonce : Words 2) (tail : BitVec 1344)
    (low₀ low₁ : BitVec 256) (message : Words 32) :
    pinnedSecondInput index nonce (replyWords (tail ++ low₀)) message =
      pinnedSecondInput index nonce (replyWords (tail ++ low₁)) message := by
  funext i
  have word (k : Nat) (hk : 4 ≤ k) (hk' : k < 25) :
      (replyWords (tail ++ low₀)) ⟨k, hk'⟩ = (replyWords (tail ++ low₁)) ⟨k, hk'⟩ := by
    change (tail ++ low₀).extractLsb' (64 * k) 64 = (tail ++ low₁).extractLsb' (64 * k) 64
    have inTail : 256 ≤ 64 * k := by omega
    exact (BitVec.extractLsb'_append_eq_of_le inTail).trans
      (BitVec.extractLsb'_append_eq_of_le inTail).symm
  unfold pinnedSecondInput
  split
  · split
    · rfl
    split
    · exact word _ (by omega) _
    · rfl
  · split
    · rfl
    split
    · rfl
    split
    · exact word _ (by omega) _
    · rfl

end TwoPermutationPrototype.Sampling
