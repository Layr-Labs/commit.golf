# Tagged permutation leaves, generated nonces, group nodes and 240-bit internal nodes

This candidate builds on submission `24f6f7fb-a42a-4b81-a9d8-2c79df9fd90e` (a two-call permutation leaf hash on
the packed-nonce cap tree of development submission `243b0d14-02c9-4f57-a5fb-1535ffcfa326`, by yukonautominer,
building on mpjunior92 and crypt0fairy; credits are in the public submission note). It changes the leaf hash, the
way nonces are made, the shape of the tree above the leaves, the width of internal nodes, and the record format.

Claimed bounds: 72,192 proof bytes, 524,638,547 commitment cycles and 168,725 opening cycles, score
37,886,886,580,224.

## Construction

```
leaf i      r_i = 16-byte nonce, tag_i = 4072 + 256 i (8 bytes)
            W1 = r_i || tag_i || v[0..176)          o1 = P(W1)
            W2 = o1[136..200) || v[120..256)        d_i = P(W2)[0..32)
group g     G_g = P(0^72 || d_4g || d_4g+1 || d_4g+2 || d_4g+3)[0..32)          g < 2^22
internal    node n = C(node 2n || node 2n+1) with bytes 30 and 31 cleared       1 <= n < 2^22
            node 2^22 + g = G_g;  commitment = node 1;  cap = nodes 256..511
nonces      seed = 32 bytes from RANDOM; block k = P(c_k || 0^160 || seed), c_k = the 8-byte address the reply is
            written to; nonces 11k .. 11k+10 are bytes 24..200 of block k (176 bytes per call)
```

`S3Leaf.lean` (`s3LeafDigest`), `S6Tree.lean` (tags, group digest, truncation) and `S4Gen.lean` (generator)
hold the definitions. Leaf bytes 120..176 enter both leaf calls; that repetition takes the place of a fixed
capacity. The tag makes every honest first-call input distinct.

## Programs

- Commitment: words 0..251,826 of the earlier image are kept except word 10 (RANDOM fills 32 seed bytes); 2,008
  words are appended (253,835 words). The generator makes 23,832 passes of 64 permutation calls. The leaf phase
  runs in blocks of 64 leaves: two permutation calls per leaf with the reply of the first call written so that
  the second window needs no copies, then 16 group calls on 368-byte cells (72 zero bytes, four leaf digests,
  room for the reply spill). The parent phase is one descending loop over the depth-22 heap: a compression call,
  a halfword store that clears bytes 30 and 31, two pointer updates. The root copy and halt are the earlier
  image's.
- Opening: 257 words. The cap opener writes the tag word and reads the three other leaf digests of the group;
  the compaction pass writes 534-byte records (nonce, the three other leaf digests of the group, the sibling
  group digest, then 13 internal siblings of 30 bytes) and a footer of 30-byte cap nodes.
- Check: 546 words. A 183-instruction leaf routine recomputes the leaf digest and the group digest; the path core
  runs 14 levels and clears bytes 30 and 31 after each compression call (two short stubs); the expansion
  wrapper restores the internal 576-byte records and 32-byte cap nodes.

## Proofs

- `S3PermModel`, `S3PermBadEvent`, `S3PermSingleCall`, `S3PermTwoCall`, `S4PermOverlap`: a lazily sampled
  permutation with forward and inverse queries, the union bound over bad events, and the collision argument for
  two calls that share an overlap field instead of a fixed capacity.
- `S3PermEager`, `S3PermStrat`, `S3PermBridge`: a uniformly sampled permutation gives exactly the event
  probabilities of the lazy model.
- `S3LeafLayout`, `S3LeafGame`, `S3LeafProbe`, `S3LeafBinding`: the leaf layout and `s3_leaf_collision_bound`.
- `S6GroupBinding`: collisions of the group node (one permutation call with 72 fixed zero bytes).
- `CompressionROM`, `BindingProbe`, `S6BindArithmetic`: collisions of compression replies truncated to 240 bits,
  and the final arithmetic.
- `S3CapBinding`, `CapBindingSecurity`, `NonceBindingSecurity` with the replay files (`Binding`, `BindingReplay`,
  `CapReplay`, `CapProbe`, `CapRecordBinding`): position binding at 120 bits for every opening size, from a
  truncated-compression collision, a leaf collision or a group collision among the replayed inputs.
- `S4PermGen`, `S4GenHide`: the generated nonces are indistinguishable from uniform ones.
- `S5PermLayer`, `S5HideLayer` and the hiding chain (`S3HidingBase`, `HidingGameIntegration`, `HidingSecurity`,
  `S3HidingTransfer`, `HidingMachine`, `HidingDistribution`, `NonceHidingSecurity`): statistical hiding with the
  whole leaf layer replaced at once.
- `S6Model`, `S6Opening`, `S6Codec`: the tree, the records and the packed format as pure functions.
- Commitment image: `S3Image`, `S3Exec`, `S4GenExec`, `S3LeafExec`, `S3LoopExec`, `S6ParentExec`, `S3TreeExec`,
  `CommitRuntime` (execution and cycles), `S4GenMemory`, `S3LeafBytes`, `S3LeafMemory`, `S3LeavesMemory`,
  `S6ParentMemory`, `CommitHeap`, `CommitOutput`, `CommitSemantics` (memory contents).
- Opening and check images: `CapOpen*`, `NonceCompact*`, `NonceOpening*` (opener and compaction);
  `S3CheckLeaf*`, `CapCheckLeaf*`, `CapCheckRecord*`, `CapCheckPath*`, `S6CheckTrunc`, `NonceExpand*`,
  `NonceCheck*` (checker); `CapHonest*`, `NonceHonest*`, `CapCompleteness`, `Budgets`, `CapBudgets`,
  `NonceProofSize`, `NonceOpeningResources` (completeness, budgets, proof size, opening cycles).
- `NonceCertificate.lean` assembles the certificate; `Solution.lean` also proves equality with the
  verifier-generated artifact for the delivered manifest (`CapPackedImageEquality`).

Security statements are in the contract's ideal model: a uniform compression function and a uniform
permutation that the adversary may query in both directions.
