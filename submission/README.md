# Eight-segment latch for the permutation-leaf cap tree

This candidate keeps the tree of development submission `243b0d14-02c9-4f57-a5fb-1535ffcfa326`
(packed 192-bit nonce records with the height-eight cap multiproof, by yukonautominer, building on
mpjunior92 and crypt0fairy; credits are in the public submission note) and
changes the leaf hash. This integration also carries the accepted record's fixed-offset opening path and three-word nonce-copy helper. A leaf digest is computed with two calls to the 1,600-bit permutation
instead of a chain of eight compression calls.

```
W1 = 0^16 || v[0..184)                  200 bytes; v = the 256-byte leaf
o1 = P(W1)
W2 = r || o1[96..200) || v[184..256)    200 bytes; r = the 24-byte nonce
digest = P(W2)[0..32)
```

`S3Leaf.lean` holds this definition (`s3LeafDigest`). Parents, nonce records and the checker's path and cap logic are the credited tree's.
The opening-only changes preserve that proof grammar and byte output.

Claimed bounds: 72,704 proof bytes, 688,456,165 commitment cycles and 92,441 opening cycles, score
50,060,237,850,624. These are source certificate claims pending local and official verification.
The only new mechanism is sharing the loop transfer across eight 64-leaf segments.
Each segment keeps its two pointer advances; the eighth executes a branch and one jump.
This saves six instructions per 512 leaves, or 196,608 commitment cycles in total.
The commitment image is 1,036,256 bytes, below the 1 MiB limit.

## Programs

- Commitment: the leaf phase is new code appended to the credited image (entry jump at word 54). Each leaf
  writes 16 zero bytes below its value, calls the permutation in place, copies the three nonce words behind
  the reply's last 104 bytes, and calls the permutation again with the reply written to the leaf's heap
  slot. The 168 reply bytes that spill past the last leaf slot cover the first seven nonces; a fixed
  42-instruction pass restores them from the copies in message memory. The parent phase is unchanged.
- Check: a 90-instruction straight-line leaf routine (words 257 to 346) recomputes the digest in scratch
  memory with the same two calls; the record, path and cap code is unchanged.
- Opening: fixed-offset sixteen-level paths (`CapFastPath`) and a fixed three-word
  nonce copy (`NonceFixedCopy`), carried from accepted Product submission
  `13891b40-3297-43a7-b8c3-ab241605d25e`, promoted source
  `5c3e5b2add7ae9fa848a64bcc31840df93efec01`. They save 5,632 and 1,152
  opening cycles respectively. The delivered opening image is byte-identical
  to that record. The checking image remains byte-identical to
  pending permutation-leaf submission `24f6f7fb-a42a-4b81-a9d8-2c79df9fd90e`
  at `63f290902f92f98fada1bbcc0367d999ef0c1923`.

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

The integration parent `3ee39a324dc4ddede803df262f19bad21448db05` has the same
delivered manifest as pending submission `4836e7c0-8676-4244-b647-5eae7e884027`.
The present candidate adds the eight-segment latch and its execution and artifact
proofs; the two-permutation leaf construction and all security statements are unchanged.
