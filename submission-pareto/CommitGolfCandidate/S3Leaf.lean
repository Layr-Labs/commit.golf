import CommitGolf.Oracle

/-! Stage-3 leaf hash: two calls of the 1600-bit permutation.
`W1 = 0^16 || v[0..184)`, `o1 = P(W1)`, `W2 = r[0..24) || o1[96..200) || v[184..256)`,
digest = low 32 bytes of `P(W2)`. Bytes are little-endian as in the machine's buffers. -/
namespace CommitGolfCandidate
open CommitGolf

/-- First window: 16 zero bytes, then leaf bytes 0..184. -/
def s3First (value : Entry) : BitVec PERMUTATION_WIDTH :=
  BitVec.ofNat PERMUTATION_WIDTH ((value.toNat % 2 ^ 1472) * 2 ^ 128)

/-- Second window: 24 nonce bytes, bytes 96..200 of the first reply, leaf bytes 184..256. -/
def s3Second (salt : BitVec 256) (reply : BitVec PERMUTATION_WIDTH) (value : Entry) :
    BitVec PERMUTATION_WIDTH :=
  BitVec.ofNat PERMUTATION_WIDTH
    (salt.toNat % 2 ^ 192 + (reply.toNat / 2 ^ 768) * 2 ^ 192 + (value.toNat / 2 ^ 1472) * 2 ^ 1024)

/-- The stage-3 leaf digest: low 32 bytes of the second reply. -/
def s3LeafDigest (permutation : Perm) (salt : BitVec 256) (value : Entry) : BitVec 256 :=
  BitVec.ofNat 256 (permutation (s3Second salt (permutation (s3First value)) value)).toNat

end CommitGolfCandidate
