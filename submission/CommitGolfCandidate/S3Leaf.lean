import CommitGolf.Oracle

/-! Leaf hash: nonce and tag in the FIRST window, two calls of the 1600-bit permutation.
`W1 = salt[0..24) || v[0..176)` where the salt field holds the 16-byte nonce and the 8-byte tag
(`tag = 4072 + 256 * index`), `o1 = P(W1)`, `W2 = o1[136..200) || v[120..256)`, digest = low 32 bytes of
`P(W2)`. Leaf bytes 120..176 enter both calls. Bytes are little-endian as in the machine's buffers.
The earlier names are kept so that every file that uses the digest abstractly is unchanged. -/
namespace CommitGolfCandidate
open CommitGolf

/-- First window: the low 24 salt bytes (nonce and tag), then leaf bytes 0..176. -/
def s3First (salt : BitVec 256) (value : Entry) : BitVec PERMUTATION_WIDTH :=
  BitVec.ofNat PERMUTATION_WIDTH (salt.toNat % 2 ^ 192 + (value.toNat % 2 ^ 1408) * 2 ^ 192)

/-- Second window: bytes 136..200 of the first reply, then leaf bytes 120..256. -/
def s3Second (reply : BitVec PERMUTATION_WIDTH) (value : Entry) : BitVec PERMUTATION_WIDTH :=
  BitVec.ofNat PERMUTATION_WIDTH (reply.toNat / 2 ^ 1088 + (value.toNat / 2 ^ 960) * 2 ^ 512)

/-- The leaf digest: low 32 bytes of the second reply. -/
def s3LeafDigest (permutation : Perm) (salt : BitVec 256) (value : Entry) : BitVec 256 :=
  BitVec.ofNat 256 (permutation (s3Second (permutation (s3First salt value)) value)).toNat

end CommitGolfCandidate
