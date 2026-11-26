import CommitGolfCandidate.TaggedPinnedModel
import CommitGolfCandidate.TwoPermutationBindingLeaf
import CommitGolfCandidate.TwoPermutationHidingBridge

/-! # The 3c1p leaf: three compressions and one permutation call

Entry `v` (256 bytes, the little-endian words `v 0 .. v 31`) at position `i` with salt `s`
(16 bytes, the words `nonce 0, nonce 1`):

* `t1 = C(v[192..256))`
* `t2 = C(v[160..192) ‖ t1)`
* `t3 = C(v[144..168) ‖ t2 ‖ t1[8..16))`
* `d  = P(v[0..144) ‖ tag i ‖ s ‖ t3)[0..32)`, with `tag i = 4096 + 256 i`, a 64-bit word.

A byte string is a little-endian bit vector: byte `k` is bits `8k .. 8k+8`. This is how the
machine's syscalls read and write memory (`readBuffer`, `packBuffer`, `read_digest_words`,
`read_compression_halves`), so the definitions below are exactly the values the commit and
check programs pass to the oracles. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.RV64

set_option autoImplicit false

/-- The position tag stored in the permutation input: the leaf's address in the message buffer. -/
def c3Tag (index : Index) : Word := BitVec.ofNat 64 (4096 + 256 * index.val)

/-- Four little-endian words as a 32-byte value (the form of `read_digest_words`). -/
def packDigestWords (w : Words 4) : BitVec 256 :=
  ((w ⟨3, by decide⟩ ++ w ⟨2, by decide⟩) ++ w ⟨1, by decide⟩) ++ w ⟨0, by decide⟩

/-- The four words of a 32-byte value, in memory order. -/
def digestWords (d : BitVec 256) : Words 4 := fun k => d.extractLsb' (64 * k.val) 64

/-- Eight little-endian words as a 64-byte compression input (the form of
`read_compression_halves`: the high half is the second 32 bytes). -/
def packWords8 (w : Words 8) : BitVec 512 :=
  packDigestWords (fun k => w ⟨k.val + 4, by omega⟩) ++ packDigestWords (fun k => w ⟨k.val, by omega⟩)

/-- Input words of the first compression: `v[192..256)`. -/
def c3FirstWords (v : Words 32) : Words 8 := fun k => v ⟨24 + k.val, by omega⟩

/-- Input words of the second compression: `v[160..192) ‖ t1`. -/
def c3SecondWords (v : Words 32) (t1 : Words 4) : Words 8 := fun k =>
  if h : k.val < 4 then v ⟨20 + k.val, by omega⟩ else t1 ⟨k.val - 4, by omega⟩

/-- Input words of the third compression: `v[144..168) ‖ t2 ‖ t1[8..16)`. -/
def c3ThirdWords (v : Words 32) (t1 t2 : Words 4) : Words 8 := fun k =>
  if h : k.val < 3 then v ⟨18 + k.val, by omega⟩
  else if h' : k.val < 7 then t2 ⟨k.val - 3, by omega⟩ else t1 1

def c3FirstInput (v : Words 32) : BitVec 512 := packWords8 (c3FirstWords v)

def c3T1 (compress : Compression) (v : Words 32) : BitVec 256 := compress (c3FirstInput v)

def c3SecondInput (compress : Compression) (v : Words 32) : BitVec 512 :=
  packWords8 (c3SecondWords v (digestWords (c3T1 compress v)))

def c3T2 (compress : Compression) (v : Words 32) : BitVec 256 := compress (c3SecondInput compress v)

def c3ThirdInput (compress : Compression) (v : Words 32) : BitVec 512 :=
  packWords8 (c3ThirdWords v (digestWords (c3T1 compress v)) (digestWords (c3T2 compress v)))

def c3T3 (compress : Compression) (v : Words 32) : BitVec 256 := compress (c3ThirdInput compress v)

/-- The 25 words of the permutation input: `v[0..144) ‖ tag ‖ salt ‖ t3`. -/
def c3PermWords (index : Index) (nonce : Words 2) (v : Words 32) (t3 : Words 4) : Words 25 := fun k =>
  if h : k.val < 18 then v ⟨k.val, by omega⟩
  else if k.val = 18 then c3Tag index
  else if h' : k.val < 21 then nonce ⟨k.val - 19, by omega⟩
  else t3 ⟨k.val - 21, by omega⟩

def c3PermInput (compress : Compression) (index : Index) (nonce : Words 2) (v : Words 32) : Block :=
  packBuffer (c3PermWords index nonce v (digestWords (c3T3 compress v)))

/-- The leaf digest: the first 32 bytes of the permutation reply. -/
def c3LeafDigest (compress : Compression) (perm : Block → Block) (index : Index) (nonce : Words 2)
    (v : Words 32) : BitVec 256 :=
  outputDigest (perm (c3PermInput compress index nonce v))

/-- The `t3` field of a permutation input: bytes `168..200`, bits `1344..1600`. -/
def c3T3Field (input : Block) : BitVec 256 := input.extractLsb' 1344 256

/-- The digest tape of an honest commitment. -/
def c3FullLeafDigests (compress : Compression) (p : BiPermutation Block) (message : Message)
    (salts : CompleteSaltTape) : DigestTape :=
  fun i => c3LeafDigest compress p.forward i (saltWords (salts i)) (messageWords message i)

/-- The honest commitment and proof as a function of the oracle, the message and the salt tape. -/
def c3HonestView (build : TranscriptBuilder) : TranscriptView :=
  fun compress p message positions salts =>
    build compress positions (fun index => salts index.val) (c3FullLeafDigests compress p message salts)

abbrev C3TranscriptRefines (scheme : Scheme) (build : TranscriptBuilder) :=
  TranscriptRefinesView scheme (c3HonestView build)

/-! ### Basic facts -/

theorem getLsbD_index {n : Nat} (x : BitVec n) {i j : Nat} (h : i = j) : x.getLsbD i = x.getLsbD j := by
  subst h; rfl

theorem true_and_of {p : Prop} [Decidable p] (h : p) (b : Bool) : (decide p && b) = b := by
  simp [h]

theorem pack_digest_words_digest (d : BitVec 256) : packDigestWords (digestWords d) = d := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [packDigestWords, digestWords, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs with h1 h2 h3 <;> rw [true_and_of (by omega)] <;> exact getLsbD_index _ (by omega)

theorem digest_words_pack (w : Words 4) : digestWords (packDigestWords w) = w := by
  funext k
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  simp only [digestWords, packDigestWords, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    true_and_of inside]
  obtain ⟨k, hk⟩ := k
  simp only [Fin.val_mk]
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> split_ifs <;> (try omega) <;> exact getLsbD_index _ (by omega)

theorem digest_words_injective : Function.Injective digestWords := by
  intro a b same
  rw [← pack_digest_words_digest a, ← pack_digest_words_digest b, same]

theorem pack_digest_words_injective : Function.Injective packDigestWords := by
  intro a b same
  rw [← digest_words_pack a, ← digest_words_pack b, same]

theorem pack_words8_injective : Function.Injective packWords8 := by
  intro a b same
  have hi := congrArg (fun x : BitVec 512 => x.extractLsb' 256 256) same
  have lo := congrArg (fun x : BitVec 512 => x.extractLsb' 0 256) same
  simp only [packWords8, BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right] at hi lo
  have hiw := pack_digest_words_injective hi
  have low := pack_digest_words_injective lo
  funext k
  by_cases small : k.val < 4
  · have := congrFun low ⟨k.val, small⟩
    simpa using this
  · have := congrFun hiw ⟨k.val - 4, by omega⟩
    have eq : (⟨k.val - 4 + 4, by omega⟩ : Fin 8) = k := Fin.ext (by simp; omega)
    simpa [eq] using this

/-- The 256 bits of a packed buffer starting at word `start` are the packed four words there. -/
theorem packed_digest_slice (words : Words 25) (start : Nat) (room : start + 4 ≤ 25) :
    (packBuffer words).extractLsb' (64 * start) 256 =
      packDigestWords (fun k => words ⟨start + k.val, by omega⟩) := by
  apply digest_words_injective
  rw [digest_words_pack]
  funext k
  apply BitVec.eq_of_getLsbD_eq
  intro bit inside
  have word := packed_word words ⟨start + k.val, by omega⟩
  have bitEq := congrArg (fun chunk : BitVec 64 => chunk.getLsbD bit) word
  simp only [BitVec.getLsbD_extractLsb', true_and_of inside] at bitEq
  simp only [digestWords, BitVec.getLsbD_extractLsb', true_and_of inside,
    true_and_of (show 64 * k.val + bit < 256 by omega)]
  rw [getLsbD_index _ (show 64 * start + (64 * k.val + bit) = 64 * (start + k.val) + bit by omega)]
  exact bitEq

theorem c3_t3_field_input (compress : Compression) (index : Index) (nonce : Words 2) (v : Words 32) :
    c3T3Field (c3PermInput compress index nonce v) = c3T3 compress v := by
  unfold c3T3Field c3PermInput
  erw [show (1344 : Nat) = 64 * 21 by decide, packed_digest_slice _ 21 (by decide)]
  conv => rhs; rw [← pack_digest_words_digest (c3T3 compress v)]
  congr 1
  funext k
  have a : ¬ (21 + k.val < 18) := by omega
  have b : ¬ (21 + k.val = 18) := by omega
  have c : ¬ (21 + k.val < 21) := by omega
  simp only [c3PermWords, a, b, c, dite_false, ite_false, show 21 + k.val - 21 = k.val by omega]

end TwoPermutationPrototype.Sampling
