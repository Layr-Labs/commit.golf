# Permutation leaf hash on the packed-nonce cap tree

This candidate keeps the tree of development submission `243b0d14-02c9-4f57-a5fb-1535ffcfa326`
(packed 192-bit nonce records with the height-eight cap multiproof, by yukonautominer, building on
mpjunior92 and crypt0fairy; credits are in the public submission note) and
changes one thing: the leaf hash. A leaf digest is computed with two calls to the 1,600-bit permutation
instead of a chain of eight compression calls.

```
W1 = 0^16 || v[0..184)                  200 bytes; v = the 256-byte leaf
o1 = P(W1)
W2 = r || o1[96..200) || v[184..256)    200 bytes; r = the 24-byte nonce
digest = P(W2)[0..32)
```

`S3Leaf.lean` holds this definition (`s3LeafDigest`). Parents, nonce records, the opening program and the
checker's path and cap logic are the credited tree's.

Claimed bounds: 72,704 proof bytes, 688,652,773 commitment cycles and 99,225 opening cycles, score
50,075,025,262,592.

## Programs

- Commitment: the leaf phase is new code appended to the credited image (entry jump at word 54). Each leaf
  writes 16 zero bytes below its value, calls the permutation in place, copies the three nonce words behind
  the reply's last 104 bytes, and calls the permutation again with the reply written to the leaf's heap
  slot. The 168 reply bytes that spill past the last leaf slot cover the first seven nonces; a fixed
  42-instruction pass restores them from the copies in message memory. The parent phase is unchanged.
- Check: a 90-instruction straight-line leaf routine (words 257 to 346) recomputes the digest in scratch
  memory with the same two calls; the record, path and cap code is unchanged.
- Opening: unchanged.

## Proofs

- `S3PermModel`, `S3PermBadEvent`, `S3PermSingleCall`, `S3PermTwoCall`, `S3PermUnary`: a lazily sampled
  permutation with forward and inverse queries, the union bound over bad events, the two-call collision
  argument, and the unary term charged to inverse queries only.
- `S3PermEager`, `S3PermStrat`, `S3PermBridge`: a uniformly sampled permutation gives exactly the event
  probabilities of the lazy model, for every fixed compression function (`perm_sampling_prob`).
- `S3LeafLayout`, `S3LeafGame`, `S3LeafProbe`, `S3LeafBinding`: the byte layout and its counts, and
  `s3_leaf_collision_bound`: two replayed leaves with different values and one digest occur with
  probability at most `(budget + 2 * extra)^2 / 2^256 + budget / 2^127`.
- `S3CapBinding`, `CapBindingSecurity`, `NonceBindingSecurity`: position binding at 120 bits for every
  opening size, from a compression collision search and a leaf collision search.
- `S3PermGhost`, `S3PermHiding`, `S3HideLayout`, `S3HideCount`, `S3HideLeaf`, the `Hiding*` chain and
  `S3HidingTransfer`: statistical hiding, one unopened leaf at a time.
- `S3Image`, `S3Exec`, `S3LeafExec`, `S3LoopExec`, `S3TreeExec`, `CommitRuntime`, `S3LeafMemory`,
  `S3LeavesMemory`, `CommitHeap`, `CommitOutput`, `CommitSemantics`: execution, cycles and memory contents of
  the commitment image.
- `S3CheckLeaf*`, `CapCheckLeaf*`, `CapCheckRecordLeaf*`: execution and result of the checker's leaf routine.
- `NonceCertificate.lean` assembles the certificate; `Solution.lean` also proves equality with the
  verifier-generated artifact for the delivered manifest.

Security statements are in the contract's ideal model: a uniform compression function and a uniform
permutation that the adversary may query in both directions.
