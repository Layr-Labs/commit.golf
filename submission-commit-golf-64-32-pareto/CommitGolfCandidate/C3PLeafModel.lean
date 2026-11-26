import CommitGolfCandidate.C3LeafModel

/-! # The paired (mirrored) 3c1p leaf

Leaf `i` has entry words `v : Words 32` (bytes `8k .. 8k+8` are word `k`) and a 16-byte salt.
Both parities make the same three compressions:

* `q = C(v[0..64))`, `r = C(v[192..256))`, `z = C(q ‖ r)`.

The permutation input is the leaf's own 200-byte window after those compressions, with the salt
at the window's outer end:

* even `i`: bytes `56 .. 256` of the leaf, `v[56..192) ‖ z ‖ tag ‖ r[8..16) ‖ salt`;
  the digest is the **last** 32 bytes of the reply;
* odd `i`: bytes `0 .. 200` of the leaf, `salt ‖ tag ‖ q[24..32) ‖ z ‖ v[64..200)`;
  the digest is the **first** 32 bytes of the reply.

The tag is the window's address in the commit image: `4096 + 256 i + 56` for even `i`,
`4096 + 256 i` for odd `i`. One 32-byte RANDOM draw per pair `(2k, 2k+1)` lands at the pair's
bytes `240 .. 272`: its first half is the even salt, its second half the odd salt.

Words and bit positions (a `Block` is `packBuffer` of 25 little-endian words, word `k` at bits
`64k .. 64k+64`):

| | even | odd |
| --- | --- | --- |
| entry words | 0..16 = `v[7..24)` | 8..24 = `v[8..25)` |
| `z` | words 17..20, bits 1088..1344 | words 4..7, bits 256..512 |
| tag | word 21 | word 2 |
| copy of `r` / `q` | word 22 = `r` word 1 | word 3 = `q` word 3 |
| salt | words 23, 24 | words 0, 1 |
| digest window of the reply | bits 1344..1600 | bits 0..256 |
-/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp TwoPermutationPrototype.RV64

set_option autoImplicit false

/-- Leaf `i` is even. -/
def c3pEven (index : Index) : Prop := index.val % 2 = 0

instance (index : Index) : Decidable (c3pEven index) := by unfold c3pEven; infer_instance

/-- The tag: the address of the leaf's permutation window in the commit image. -/
def c3pTag (index : Index) : Word :=
  if c3pEven index then BitVec.ofNat 64 (4096 + 256 * index.val + 56) else BitVec.ofNat 64 (4096 + 256 * index.val)

/-- Input words of `q = C(v[0..64))`. -/
def c3pQWords (v : Words 32) : Words 8 := fun k => v ⟨k.val, by omega⟩

/-- Input words of `r = C(v[192..256))`. -/
def c3pRWords (v : Words 32) : Words 8 := fun k => v ⟨24 + k.val, by omega⟩

/-- Input words of `z = C(q ‖ r)`. -/
def c3pZWords (q r : Words 4) : Words 8 := fun k =>
  if h : k.val < 4 then q ⟨k.val, h⟩ else r ⟨k.val - 4, by omega⟩

def c3pQInput (v : Words 32) : BitVec 512 := packWords8 (c3pQWords v)

def c3pQ (compress : Compression) (v : Words 32) : BitVec 256 := compress (c3pQInput v)

def c3pRInput (v : Words 32) : BitVec 512 := packWords8 (c3pRWords v)

def c3pR (compress : Compression) (v : Words 32) : BitVec 256 := compress (c3pRInput v)

def c3pZInput (compress : Compression) (v : Words 32) : BitVec 512 :=
  packWords8 (c3pZWords (digestWords (c3pQ compress v)) (digestWords (c3pR compress v)))

def c3pZ (compress : Compression) (v : Words 32) : BitVec 256 := compress (c3pZInput compress v)

/-- Even window: `v[56..192) ‖ z ‖ tag ‖ r[8..16) ‖ salt`. -/
def c3pEvenWords (index : Index) (nonce : Words 2) (v : Words 32) (z r : Words 4) : Words 25 := fun k =>
  if h : k.val < 17 then v ⟨7 + k.val, by omega⟩
  else if h' : k.val < 21 then z ⟨k.val - 17, by omega⟩
  else if k.val = 21 then c3pTag index
  else if k.val = 22 then r 1
  else nonce ⟨k.val - 23, by omega⟩

/-- Odd window: `salt ‖ tag ‖ q[24..32) ‖ z ‖ v[64..200)`. -/
def c3pOddWords (index : Index) (nonce : Words 2) (v : Words 32) (z q : Words 4) : Words 25 := fun k =>
  if h : k.val < 2 then nonce ⟨k.val, h⟩
  else if k.val = 2 then c3pTag index
  else if k.val = 3 then q 3
  else if h' : k.val < 8 then z ⟨k.val - 4, by omega⟩
  else v ⟨k.val, by omega⟩

def c3pPermWords (compress : Compression) (index : Index) (nonce : Words 2) (v : Words 32) : Words 25 :=
  if c3pEven index then
    c3pEvenWords index nonce v (digestWords (c3pZ compress v)) (digestWords (c3pR compress v))
  else
    c3pOddWords index nonce v (digestWords (c3pZ compress v)) (digestWords (c3pQ compress v))

def c3pPermInput (compress : Compression) (index : Index) (nonce : Words 2) (v : Words 32) : Block :=
  packBuffer (c3pPermWords compress index nonce v)

/-- The `z` field of an even input (words 17..20) and of an odd input (words 4..7). -/
def c3pEvenZField (input : Block) : BitVec 256 := input.extractLsb' 1088 256

def c3pOddZField (input : Block) : BitVec 256 := input.extractLsb' 256 256

/-- The even digest window: the last 32 bytes of a reply. The odd window is `outputDigest`. -/
def c3pEvenDigest (reply : Block) : BitVec 256 := reply.extractLsb' 1344 256

def c3pDigestWindow (index : Index) (reply : Block) : BitVec 256 :=
  if c3pEven index then c3pEvenDigest reply else outputDigest reply

/-- The leaf digest. -/
def c3pLeafDigest (compress : Compression) (perm : Block → Block) (index : Index) (nonce : Words 2)
    (v : Words 32) : BitVec 256 :=
  c3pDigestWindow index (perm (c3pPermInput compress index nonce v))

/-- The digest tape of an honest commitment. -/
def c3pFullLeafDigests (compress : Compression) (p : BiPermutation Block) (message : Message)
    (salts : CompleteSaltTape) : DigestTape :=
  fun i => c3pLeafDigest compress p.forward i (saltWords (salts i)) (messageWords message i)

/-- The honest commitment and proof as a function of the oracle, the message and the salt tape. -/
def c3pHonestView (build : TranscriptBuilder) : TranscriptView :=
  fun compress p message positions salts =>
    build compress positions (fun index => salts index.val) (c3pFullLeafDigests compress p message salts)

abbrev C3PTranscriptRefines (scheme : Scheme) (build : TranscriptBuilder) :=
  TranscriptRefinesView scheme (c3pHonestView build)

/-! ### Basic facts -/

theorem c3p_tag_injective : Function.Injective c3pTag := by
  intro a b same
  have value := congrArg BitVec.toNat same
  have ha := a.isLt
  have hb := b.isLt
  have la : (LENGTH : Nat) = 2 ^ 24 := rfl
  unfold c3pTag c3pEven at value
  apply Fin.ext
  split_ifs at value <;> simp only [BitVec.toNat_ofNat] at value <;>
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at value <;> omega

theorem c3p_even_z_field (compress : Compression) (index : Index) (even : c3pEven index) (nonce : Words 2)
    (v : Words 32) : c3pEvenZField (c3pPermInput compress index nonce v) = c3pZ compress v := by
  unfold c3pEvenZField c3pPermInput
  erw [show (1088 : Nat) = 64 * 17 by decide, packed_digest_slice _ 17 (by decide)]
  conv => rhs; rw [← pack_digest_words_digest (c3pZ compress v)]
  congr 1
  funext k
  have a : ¬ (17 + k.val < 17) := by omega
  have b : 17 + k.val < 21 := by omega
  simp only [c3pPermWords, even, ite_true, c3pEvenWords, a, b, dite_false, dite_true,
    show 17 + k.val - 17 = k.val by omega]

theorem c3p_odd_z_field (compress : Compression) (index : Index) (odd : ¬ c3pEven index) (nonce : Words 2)
    (v : Words 32) : c3pOddZField (c3pPermInput compress index nonce v) = c3pZ compress v := by
  unfold c3pOddZField c3pPermInput
  have slice := packed_digest_slice (c3pPermWords compress index nonce v) 4 (by decide)
  rw [show 64 * 4 = 256 by rfl] at slice
  erw [slice]
  conv => rhs; rw [← pack_digest_words_digest (c3pZ compress v)]
  congr 1
  funext k
  have a : ¬ (4 + k.val < 2) := by omega
  have b : ¬ (4 + k.val = 2) := by omega
  have c : ¬ (4 + k.val = 3) := by omega
  have d : 4 + k.val < 8 := by omega
  simp only [c3pPermWords, odd, ite_false, c3pOddWords, a, b, c, d, dite_false, dite_true, ite_false,
    show 4 + k.val - 4 = k.val by omega]

end TwoPermutationPrototype.Sampling
