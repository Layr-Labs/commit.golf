# Overlap leaf hash on the packed-nonce cap tree (no zero prefix)

This candidate keeps the tree, nonce records, cap multiproof and opening program of the accepted
submission `0e8db69f-ffbd-4064-85e6-c64ca28cf018` (e-man07), which carries the two-permutation leaf hash
of `24f6f7fb-a42a-4b81-a9d8-2c79df9fd90e` (kshitij-hash) and the opening work of `4836e7c0` (kaankolcu),
all on the development tree `243b0d14-02c9-4f57-a5fb-1535ffcfa326` (yukonautominer, mpjunior92,
crypt0fairy). It changes one thing: the byte layout of the leaf hash, so that the commitment no longer
stores 16 zero bytes in front of every leaf.

```
W1 = v[0..200)                              200 bytes; v = the 256-byte leaf, no prefix
o1 = P(W1)
W2 = o1[120..176) || r || v[136..256)       56 + 24 + 120 bytes; r = the 24-byte nonce
digest = P(W2)[0..32)
```

Leaf bytes 136..200 are read by both calls. `S3Leaf.lean` holds the definition (`s3LeafDigest`).

The same idea (an overlap in place of the zero prefix, same cycle count) was filed earlier by i34-9 as
`95bf06c` with a different byte layout; this tree was written independently and in parallel, see the
public note.

Claimed bounds: 72,704 proof bytes, 655,098,341 commitment cycles and 64,281 opening cycles, score
47,632,943,269,888.

## Programs

- Commitment: each unrolled leaf is 12 instructions and 26 cycles (was 14 and 28):
  `addi a2,a0,-64; ecall; ld/sd x3 (nonce to 112..136 above the leaf); addi a0,a0,56; addi a2,s7,32u;
  ecall; addi a0,a0,200`. The first reply is written 64 bytes below the leaf, so its bytes 120..176 end
  where the nonce copy starts and leaf bytes 136..256 stay in place. Groups of 64 leaves, the
  three-instruction latch, the 42-instruction nonce repair (now reading the copies at leaf byte 112) and
  the exit are as before. The appended block is 821 words (was 949); the image is 252,648 words.
  Exact cost of the leaf phase: `1667 * 2^18 + 50` cycles, `2 * 2^24` fewer than before.
- Check: the leaf routine is still 90 instructions and 104 cycles, so every count in the checker
  certificate is unchanged. The first call reads the claimed value in place at `x8` and writes its reply
  at scratch 0; reply bytes 120..176, the nonce and value bytes 136..256 are then copied to scratch
  0..200 for the second call. 22 filler instructions keep the length. Only scratch below 288 is written.
- Opening: unchanged (the opener of `0e8db69f`).

## Proofs

- `S3Overlap` (new): the two-call hash with an overlap instead of a sparse first-call range. Seven bad
  events (digest collision, chain collision, inverse hit of a chaining slot, forward hit of a chaining
  slot, an inverse-created first window matching the overlap of an older second window, an
  inverse-created first window with the overlap of an older first window, and the lone inverse self
  loop), the deterministic extraction `overlap_collision_imp_bad` and the bound
  `overlap_prob_not_good_le`, both inside the lazy-permutation framework of `24f6f7fb`.
- `S3LeafLayout`, `S3LeafGame`, `S3LeafBinding`: the layout as a `TwoCall` instance with its counts
  (`2^1344` states per digest, `2^1152` per chaining value and per chaining slot, `2^1088` first windows
  per overlap) and the leaf collision bound `(budget + 2 extra)^2 / 2^256 + budget / 2^127`, the same
  statement as before, so the cap binding argument above it is untouched.
- `S3HideLayout`, `S3HideCount`, `S3HideLeaf`: the generic two-call hiding bound of `24f6f7fb`
  instantiated at the new sizes (192-bit nonce in the second call, 960-bit second message part).
- `S3CommitRef`, `S3Image`, `S3LeafExec`, `S3LoopExec`, `S3TreeExec`, `CommitRuntime`: the new leaf
  loop on the interpreter, with the exact cycle count.
- `S3LeafBytes`, `S3LeafMemory`, `S3LeavesMemory`: every heap slot receives the digest of its leaf under
  its nonce and the nonce region is the sampled one after the repair.
- `CapPrograms`, `CapCheckLeafImage`, `S3CheckLeafRun`, `S3CheckLeafStates`, `CapCheckLeafFrame`,
  `CapCheckLeafSemantics`: the new checker leaf routine, its execution, frame and digest.

Security statements are in the contract's ideal model: a uniform compression function and a uniform
permutation that the adversary may query in both directions.
