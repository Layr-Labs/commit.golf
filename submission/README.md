# Pinned permutation leaf: no capacity stores

This candidate keeps the tree, nonce records, cap multiproof and fixed-offset opening program of
the accepted submission `4836e7c0` (two-permutation leaves with fixed-offset opening, by kaankolcu),
and the two-permutation leaf of `24f6f7fb` (permutation leaf hash, by kshitij-hash), which build on
`243b0d14` (packed 192-bit nonce records with the height-eight cap multiproof), `f3d52eaa` and the
192-bit nonce commitment loop of `22ab66cc`; credits for that lineage are in the public submission
notes. It changes one thing: the byte layout of the leaf hash, so that the
commitment no longer writes the 16 zero bytes in front of every leaf.

```
W1 = v[0..200)                           200 bytes; v = the 256-byte leaf (no zero prefix)
o1 = P(W1)
W2 = r || o1[112..200) || v[168..256)    24 + 88 + 88 bytes; r = the 24-byte nonce
digest = P(W2)[0..32)
```

The leaf bytes `v[168..200)` are absorbed by both calls. They pin the first window inside the
second: an inverse query that is to produce a first window matching a given second window has to
hit those 256 bits, and two first windows with one chaining value and one pin are a 256-bit
collision. This replaces the fixed 128-bit zero prefix of the previous layout.

Claimed bounds: 72,704 proof bytes, 655,098,341 commitment cycles and 92,441 opening cycles,
score 47,634,990,614,528.

## Programs

- Commitment: each unrolled leaf is now 12 words (10 ordinary instructions, 26 cycles, was 14 words
  and 28 cycles). The first call reads the leaf in place and writes its reply 32 bytes below it,
  so the reply ends at leaf byte 168; the three nonce words are copied over reply bytes 88..112
  (leaf bytes 56..80); the second call reads `W2` at leaf byte 56 and writes the heap slot. The
  latch, the nonce repair and the parent phase are unchanged; 128 unreachable padding words keep
  the image length. Exact cost: `1667 * 2^18 + 50` leaf-phase cycles, 2 * 2^24 fewer than before.
- Check: the 90-word leaf routine copies the value's first 200 bytes to scratch, calls the
  permutation, copies the nonce and value bytes 200..256 next to the reply, and calls it again.
- Opening: unchanged (the fixed-offset opener of `4836e7c0`).

## Proofs

- Binding: `S3PermPinCall` is a pinned two-call hash with six pair bad events (digest and chaining
  collisions, forward or inverse hits of a chaining slot, and inverse answers matching an older pin)
  and one unary event; every bad event has at most `2^1345 + 2^897` bad answers per older entry,
  so the leaf collision bound `(budget + 2 * extra)^2 / 2^256 + budget / 2^127` of the previous
  candidate still holds verbatim and the cap binding argument is unchanged.
- Hiding: the generic two-call hiding argument applies with the 88 pinned-and-new leaf bytes as the
  second message part; the salt is still a fresh 192-bit value in the second call.
- Machine: `S3LeafExec`, `S3LoopExec`, `S3TreeExec`, `CommitRuntime`, `S3LeafBytes`,
  `S3LeafMemory`, `S3LeavesMemory` re-prove execution, cycles and memory of the new leaf loop;
  the checker's leaf routine proofs are re-done for the new routine.

Security statements are in the contract's ideal model: a uniform compression function and a
uniform permutation that the adversary may query in both directions.
