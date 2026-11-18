import CommitGolfCandidate.S6Tree

/-! Nonce generator: the 16-byte nonces are replies of the 1600-bit permutation in
counter mode under a 32-byte seed.

Call `k` reads the 200-byte block `counter(8) || 0^160 || seed(32)`; the counter is the address
the reply is written to, `6106910984 + 176 * k` (nonce base 6106911008 minus 24, plus 176 k).
Reply bytes 24..200 are the nonces of leaves `11k .. 11k+10`; reply bytes 0..24 are overwritten
by the next reply (the last one by leaf-phase spill) and never leave the machine. Definitions only. -/
namespace CommitGolfCandidate
open CommitGolf

/-- Generator calls made by the commitment program (64 per loop pass, 23,832 passes). -/
def S4_GEN_CALLS : Nat := 1525248

/-- Blocks that hold a nonce of some leaf: `ceil(2^24 / 11)`. -/
def S4_GEN_BLOCKS : Nat := 1525202

/-- Input of generator call `k`: reply address, 160 zero bytes, seed. -/
def s4GenInput (seed : BitVec 256) (k : Nat) : BitVec PERMUTATION_WIDTH :=
  BitVec.ofNat PERMUTATION_WIDTH ((6106910984 + 176 * k) + seed.toNat * 2 ^ 1344)

/-- Nonce of leaf `index`: 16 reply bytes of block `index / 11`, from byte `24 + 16 * (index % 11)`. -/
def s4GenNonce (permutation : Perm) (seed : BitVec 256) (index : Index) : Nonce128 :=
  BitVec.ofNat 128
    ((permutation (s4GenInput seed (index.val / 11))).toNat / 2 ^ (192 + 128 * (index.val % 11)))

end CommitGolfCandidate
