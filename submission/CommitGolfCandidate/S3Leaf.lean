import CommitGolf.Oracle

/-! Stage-3 leaf hash, overlap layout: two calls of the 1600-bit permutation and no fixed prefix.
`W1 = v[0..200)`, `o1 = P(W1)`, `W2 = o1[120..176) || r[0..24) || v[136..256)`,
digest = low 32 bytes of `P(W2)`. Leaf bytes 136..200 are read by both calls.
Bytes are little-endian as in the machine's buffers. -/
namespace CommitGolfCandidate
open CommitGolf

/-- First window: leaf bytes 0..200. -/
def s3First (value : Entry) : BitVec PERMUTATION_WIDTH :=
  BitVec.ofNat PERMUTATION_WIDTH value.toNat

/-- Second window: bytes 120..176 of the first reply, 24 nonce bytes, leaf bytes 136..256. -/
def s3Second (salt : BitVec 256) (reply : BitVec PERMUTATION_WIDTH) (value : Entry) :
    BitVec PERMUTATION_WIDTH :=
  BitVec.ofNat PERMUTATION_WIDTH
    (reply.toNat / 2 ^ 960 % 2 ^ 448 + (salt.toNat % 2 ^ 192) * 2 ^ 448 +
      (value.toNat / 2 ^ 1088) * 2 ^ 640)

/-- The stage-3 leaf digest: low 32 bytes of the second reply. -/
def s3LeafDigest (permutation : Perm) (salt : BitVec 256) (value : Entry) : BitVec 256 :=
  BitVec.ofNat 256 (permutation (s3Second salt (permutation (s3First value)) value)).toNat

end CommitGolfCandidate
