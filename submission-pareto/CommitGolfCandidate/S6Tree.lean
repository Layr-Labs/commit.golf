import CommitGolfCandidate.S3Leaf
import CommitGolfCandidate.NonceEncoding

/-! Tree pieces above the leaf digest. Definitions only.

* the tagged salt of a leaf: 16-byte nonce, then the 8-byte tag `4072 + 256 * index`;
* the group digest of four leaf digests: one permutation call on 72 zero bytes and the digests;
* the truncating compression: every internal node keeps 240 bits (top two bytes zero). -/
namespace CommitGolfCandidate
open CommitGolf

/-- 16-byte nonces. -/
abbrev Nonce128 := BitVec 128

/-- The tag of a leaf: the address of its first window (leaf address minus 24). -/
def s6Tag (index : Index) : Nat := 4072 + 256 * index.val

/-- The 256-bit salt field of a leaf: nonce (16 bytes), tag (8 bytes), 8 zero bytes. -/
def expandTagged (index : Index) (nonce : Nonce128) : BitVec 256 :=
  BitVec.ofNat 256 (nonce.toNat + s6Tag index * 2 ^ 128)

/-- The salt vector of the tree for a nonce vector. -/
def expandTaggedVector (nonce : Index → Nonce128) : Index → BitVec 256 :=
  fun index => expandTagged index (nonce index)

/-- Window of the group call: 72 zero bytes, then the four leaf digests in order. -/
def s6GroupInput (d0 d1 d2 d3 : BitVec 256) : BitVec PERMUTATION_WIDTH :=
  BitVec.ofNat PERMUTATION_WIDTH
    ((d0.toNat + d1.toNat * 2 ^ 256 + d2.toNat * 2 ^ 512 + d3.toNat * 2 ^ 768) * 2 ^ 576)

/-- Digest of a group of four leaves: low 32 bytes of the reply. -/
def s6GroupDigest (permutation : Perm) (d0 d1 d2 d3 : BitVec 256) : BitVec 256 :=
  BitVec.ofNat 256 (permutation (s6GroupInput d0 d1 d2 d3)).toNat

/-- Keep the low 240 bits of a digest (bytes 30 and 31 become zero). -/
def s6Trunc (digest : BitVec 256) : BitVec 256 := BitVec.ofNat 256 (digest.toNat % 2 ^ 240)

/-- The compression used at every internal node: the oracle reply with its top two bytes cleared. -/
def s6Compress (compress : Compression) : Compression := fun input => s6Trunc (compress input)

end CommitGolfCandidate
