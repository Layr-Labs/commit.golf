import CommitGolfCandidate.PairLeafModel
import CommitGolfCandidate.TwoPermutationPinnedStoredLeaf

/-!
# The even pair-heads leaf as a pinned two-call hash (binding side)

`evenPinCall` is the `PinCall` instance (S3PermPinCall.lean) behind `evenLeafDigest` (PairLeafModel.lean):

* first-call input `x1`: value bytes 56..256 (1600 bits), the whole first window (`enc1` is the identity);
* pinned part of a first-call input: its bytes 0..80 (640 bits, = value bytes 56..136);
* chaining value: bytes 160..200 of a reply (320 bits);
* second-call input, from bit 0: tag (64) | chain (320) | value bytes 0..56 (448) | pinned part (640) | salt (128).
  The salt slot is `R = BitVec 128 × BitVec 64` (salt, tag).
* digest: bytes 0..32 of a reply.

Counts: `2^1344` states per digest, `2^1280` per chaining value, `2^960` per pinned part, `2^1280` second-call
inputs per chaining slot, so `k = 2^1344 + 2^1281` bounds the bad answers of both fresh forward and fresh inverse
queries and the unary term has at most `2^1280` bad answers.
-/

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation TwoPermutationPrototype.RV64 Finset
set_option maxRecDepth 8192
set_option exponentiation.threshold 2100

theorem even_append_split {w w' : Nat} {a a' : BitVec w} {b b' : BitVec w'} (same : a ++ b = a' ++ b') :
    a = a' ∧ b = b' :=
  ⟨by simpa only [BitVec.extractLsb'_append_eq_left] using congrArg (fun x => x.extractLsb' w' w) same,
   by simpa only [BitVec.extractLsb'_append_eq_right] using congrArg (fun x => x.extractLsb' 0 w') same⟩

theorem even_enc2_injective :
    Function.Injective fun i : (BitVec 128 × BitVec 64) × BitVec 320 × BitVec 640 × BitVec 448 =>
      (i.1.1 ++ (i.2.2.1 ++ (i.2.2.2 ++ (i.2.1 ++ i.1.2))) : S3State) := by
  rintro ⟨⟨s, t⟩, c, p, m⟩ ⟨⟨s', t'⟩, c', p', m'⟩ h
  obtain ⟨hs, h⟩ := even_append_split h
  obtain ⟨hp, h⟩ := even_append_split h
  obtain ⟨hm, h⟩ := even_append_split h
  obtain ⟨hc, ht⟩ := even_append_split h
  subst hs hp hm hc ht
  rfl

/-- The even leaf hash as a pinned two-call hash on the 1600-bit state. The salt slot is
`(salt, tag)`; the second-call input is `salt | pin | value bytes 0..56 | chain | tag` (high to low). -/
def evenPinCall : PinCall S3State (BitVec 1600) (BitVec 128 × BitVec 64) (BitVec 320) (BitVec 640)
    (BitVec 448) (BitVec 256) where
  enc1 x := x
  enc1_inj := fun _ _ same => same
  pin s := s.extractLsb' 0 640
  chop o := o.extractLsb' 1280 320
  enc2 i := i.1.1 ++ (i.2.2.1 ++ (i.2.2.2 ++ (i.2.1 ++ i.1.2)))
  enc2_inj := even_enc2_injective
  trunc := s3PinCall.trunc

/-! ### Counts -/

theorem even_second_inputs :
    Fintype.card (BitVec 128 × BitVec 64) * Fintype.card (BitVec 640) * Fintype.card (BitVec 448) ≤
      2 ^ 1280 := by
  rw [Fintype.card_prod, s3_card_bitvec, s3_card_bitvec, s3_card_bitvec, s3_card_bitvec, ← pow_add, ← pow_add,
    ← pow_add]

theorem even_chop_fiber (c : BitVec 320) :
    (univ.filter fun s : S3State => evenPinCall.chop s = c).card ≤ 2 ^ 1280 := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter fun s : S3State => evenPinCall.chop s = c)
    (t := (univ : Finset (BitVec 1280))) (fun s => s.extractLsb' 0 1280)
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have high : a.extractLsb' 1280 320 = b.extractLsb' 1280 320 := ha.trans hb.symm
      have low : a.extractLsb' 0 1280 = b.extractLsb' 0 1280 := hab
      have ra := BitVec.extractLsb'_append_extractLsb' (w := 320) (len := 1280) (x := a)
      have rb := BitVec.extractLsb'_append_extractLsb' (w := 320) (len := 1280) (x := b)
      rw [high, low] at ra
      exact ra.symm.trans rb)
  rwa [Finset.card_univ, s3_card_bitvec] at h

theorem even_pin_fiber (p : BitVec 640) :
    (univ.filter fun s : S3State => evenPinCall.pin s = p).card ≤ 2 ^ 960 := by
  have h := Finset.card_le_card_of_injOn (s := univ.filter fun s : S3State => evenPinCall.pin s = p)
    (t := (univ : Finset (BitVec 960))) (fun s => s.extractLsb' 640 960)
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have low : a.extractLsb' 0 640 = b.extractLsb' 0 640 := ha.trans hb.symm
      have high : a.extractLsb' 640 960 = b.extractLsb' 640 960 := hab
      have ra := BitVec.extractLsb'_append_extractLsb' (w := 960) (len := 640) (x := a)
      have rb := BitVec.extractLsb'_append_extractLsb' (w := 960) (len := 640) (x := b)
      rw [high, low] at ra
      exact ra.symm.trans rb)
  rwa [Finset.card_univ, s3_card_bitvec] at h

theorem even_trunc_fiber (d : BitVec 256) :
    (univ.filter fun s : S3State => evenPinCall.trunc s = d).card ≤ 2 ^ 1344 :=
  s3_trunc_fiber d

/-! ### The machine layout of the two even calls -/

private theorem even_block_eq_of_words (a b : BitVec 1600)
    (words : ∀ j : Fin 25, a.extractLsb' (64 * j.val) 64 = b.extractLsb' (64 * j.val) 64) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  have same := congrArg (fun chunk : BitVec 64 => chunk.getLsbD (bit % 64)) (words ⟨bit / 64, by omega⟩)
  have inner : bit % 64 < 64 := by omega
  have address : 64 * (bit / 64) + bit % 64 = bit := by omega
  simpa [inner, address] using same

private theorem even_nested_slice {size : Nat} (word : BitVec size) {outer width start len : Nat}
    (room : start + len ≤ width) :
    (word.extractLsb' outer width).extractLsb' start len = word.extractLsb' (outer + start) len := by
  apply BitVec.eq_of_getLsbD_eq
  intro i inside
  have mid : start + i < width := by omega
  simp [mid, inside, Nat.add_assoc]

theorem even_pack_first (value : Entry) :
    packBuffer (evenFirstInput (entryWords value)) = value.extractLsb' 448 1600 := by
  apply even_block_eq_of_words
  intro j
  rw [packed_word, even_nested_slice _ (by have := j.isLt; omega)]
  change value.extractLsb' (64 * (j.val + 7)) 64 = _
  congr 1
  omega

theorem even_pack_second (index : Index) (value : Entry) (reply : Block) (salt : BitVec 128) :
    packBuffer (evenSecondInput index (saltWords salt) (replyWords reply) (entryWords value)) =
      salt ++ ((value.extractLsb' 448 1600).extractLsb' 0 640 ++ (value.extractLsb' 0 448 ++
        (reply.extractLsb' 1280 320 ++ evenPositionTag index))) := by
  apply even_block_eq_of_words
  intro j
  rw [packed_word]
  have fits := j.isLt
  by_cases zero : j.val = 0
  · simp only [evenSecondInput, zero, ite_true, Nat.mul_zero]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 1472),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 832),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 384),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64)]
    exact BitVec.extractLsb'_eq_self.symm
  · by_cases chainWord : j.val < 6
    · simp only [evenSecondInput, zero, ite_false, chainWord, dite_true, replyWords]
      rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 1472),
        BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 832),
        BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 384),
        BitVec.extractLsb'_append_eq_of_le (by omega : 64 ≤ 64 * j.val),
        even_nested_slice _ (by omega : 64 * j.val - 64 + 64 ≤ 320)]
      congr 1
      omega
    · by_cases lowWord : j.val < 13
      · have messageWord : j.val < 23 := by omega
        simp only [evenSecondInput, zero, ite_false, chainWord, messageWord, dite_false, dite_true,
          entryWords]
        rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 1472),
          BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 832),
          BitVec.extractLsb'_append_eq_of_le (by omega : 384 ≤ 64 * j.val),
          even_nested_slice _ (by omega : 64 * j.val - 384 + 64 ≤ 448)]
        congr 1
        omega
      · by_cases messageWord : j.val < 23
        · simp only [evenSecondInput, zero, ite_false, chainWord, messageWord, dite_false, dite_true,
            entryWords]
          rw [BitVec.extractLsb'_append_eq_of_add_le (by omega : 64 * j.val + 64 ≤ 1472),
            BitVec.extractLsb'_append_eq_of_le (by omega : 832 ≤ 64 * j.val),
            even_nested_slice _ (by omega : 64 * j.val - 832 + 64 ≤ 640),
            even_nested_slice _ (by omega : 0 + (64 * j.val - 832) + 64 ≤ 1600)]
          congr 1
          omega
        · simp only [evenSecondInput, zero, ite_false, chainWord, messageWord, dite_false, saltWords]
          rw [BitVec.extractLsb'_append_eq_of_le (by omega : 1472 ≤ 64 * j.val)]
          congr 1
          omega

/-- The leaf input of an even leaf: first window, (salt, tag), value bytes 0..56. -/
def evenInput (index : Index) (salt : BitVec 128) (value : Entry) :
    BitVec 1600 × (BitVec 128 × BitVec 64) × BitVec 448 :=
  (value.extractLsb' 448 1600, (salt, evenPositionTag index), value.extractLsb' 0 448)

theorem even_input_ne (index index' : Index) (salt salt' : BitVec 128) {value value' : Entry}
    (different : value ≠ value') : evenInput index salt value ≠ evenInput index' salt' value' := by
  intro same
  apply different
  have h1 : value.extractLsb' 448 1600 = value'.extractLsb' 448 1600 := congrArg (fun p => p.1) same
  have h2 : value.extractLsb' 0 448 = value'.extractLsb' 0 448 := congrArg (fun p => p.2.2) same
  have ra := BitVec.extractLsb'_append_extractLsb' (w := 1600) (len := 448) (x := value)
  have rb := BitVec.extractLsb'_append_extractLsb' (w := 1600) (len := 448) (x := value')
  exact ra.symm.trans ((congrArg₂ (· ++ ·) h1 h2).trans rb)

theorem even_first_eq (index : Index) (salt : BitVec 128) (value : Entry) :
    packBuffer (evenFirstInput (entryWords value)) = evenPinCall.enc1 (evenInput index salt value).1 :=
  even_pack_first value

theorem even_second_eq (index : Index) (value : Entry) (reply : Block) (salt : BitVec 128) :
    packBuffer (evenSecondInput index (saltWords salt) (replyWords reply) (entryWords value)) =
      evenPinCall.enc2 ((evenInput index salt value).2.1, evenPinCall.chop reply,
        evenPinCall.pin (evenPinCall.enc1 (evenInput index salt value).1), (evenInput index salt value).2.2) :=
  even_pack_second index value reply salt

end TwoPermutationPrototype.Sampling
