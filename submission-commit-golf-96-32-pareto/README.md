# A pair-slot cap on dadon's 3e63809d: 959,487,715 cycles at 71,680 bytes

This entry is dadon's promoted `commit-golf-96-32-product` entry `3e63809d` (16-byte salts with an 8-byte address tag) with a different encoding of the top of the tree in 128-position openings. The commitment program, the leaves, the tree and the commitment value are `3e63809d`'s; only the opening and check programs change, and with them the batch proof format.

| Entry | Commit cycles | Opening cycles | Prover cycles | Proof bytes |
| --- | ---: | ---: | ---: | ---: |
| `3e63809d` (dadon) | 959,447,084 | 40,102 | 959,487,186 | 75,776 |
| This entry | 959,447,084 | 40,631 | 959,487,715 | 71,680 |

`claim.json` is `{"proofBytes": 71680, "commitCycles": 959447084, "openingCycles": 40631}`. The product is 68,776,079,411,200, 5.41% below `3e63809d`'s 72,706,101,006,336.

## What changed

`3e63809d` sends, at 128 positions, 128 records of a 16-byte salt and 17 siblings (depths 24 down to 8, counting the root as depth 0) and then the 128 depth-7 digests. Here each record stops one level lower, after 16 siblings (depths 24 down to 9), at its level-8 node, and the proof ends with one 32-byte slot for each of the 128 pairs of level-8 nodes:

- a pair with no opened position below it gets its level-7 parent;
- a pair with an opened position below it gets the level-8 sibling of its first opened position. The checker uses the slot only when exactly one child of the pair is reached by a record; when both are, it hashes their computed digests and ignores the slot, which is safe because both are bound through the parent and the root.

The checker hashes each record up to its level-8 node, rejects if two records reach the same node with different values, computes each level-7 node by hashing its pair when a record reaches the pair and takes it from the slot otherwise, then hashes the upper tree to the commitment. Records are 16 + 16 x 32 = 528 bytes: 128 x 528 + 128 x 32 = 71,680 bytes, 4,096 fewer than `3e63809d`. Openings of other sizes keep `3e63809d`'s full paths. Every 128-position opening takes exactly 40,631 cycles and makes no oracle calls; the checker makes at most 2,815 calls at 128 positions.

## Why the certificate holds

- Hiding: the new batch proof is a fixed byte-level function of `3e63809d`'s proof for the same positions (drop each record's last sibling and fill the pair slots from the old records and cap), with no oracle calls, so `3e63809d`'s hiding bound (its tagged-salt argument, `HidingTaggedSalt.lean`, unchanged here) transfers unchanged.
- Binding: `PairBinding` reduces two accepted openings that disagree at a position to a compression collision, as `3e63809d`'s reduction does, with at most 10,928 calls beyond the adversary's; the duplicate comparison and the root comparison are proved for adversarial bytes.
- Machine proofs: the theorem `PairCap.batchEvaluation` proves, for every correctly sized batch input including malicious bytes, that the new checker terminates, makes at most 2,815 calls and accepts exactly when the abstract batch predicate holds; the opener is proved to emit the new format in exactly 40,631 cycles.

New modules: 83 `Pair*` modules (`PairImage`, `PairStatic`, `PairOpening`, `PairWords`, `PairSuffix`, `PairInput`, `PairResources`, `PairFormat`, `PairPrivacy`, `PairControl`, `PairChildren`, `PairBatchModel`, `PairHash`, `PairUpper`, `PairSound`, `PairReplay`, `PairExtractor`, `PairBinding`, `PairProgress`, `PairEvaluation`, `PairCertificate` and their helpers). Changed: `Opening.lean` (exposes helpers) and `Solution.lean`. Every other module of `3e63809d`, including the tagged leaf, `HidingTaggedSalt.lean` and the commitment proofs, is unchanged.

## Credits

The commitment scheme, its programs and its certificate are dadon's `3e63809d`, which builds on dadon's `c9b8af82`, AdamGagol's `3839a36d` and `7e8904fd` and the organizers' baseline; its README follows unchanged below. The pair-slot cap is the same encoding as in our Stage 1 on `c9b8af82`.

---

# commit-golf-96-32-product: 128-bit tagged salt, 32×32 unrolled gap-heap, and level-7 cap table

This is a salted binary Merkle commitment over the track's 96→32-byte compression
oracle. Compression costs eight cycles; forward and inverse permutation calls
cost 30. The programs use compression only.

## Construction

Each 2048-bit leaf `i` uses a private 16-byte (128-bit) salt paired with its
unique 8-byte leaf-slot tag `4072 + 256 * i` and is absorbed in four direct
96-byte compression calls:

1. Call 0 compresses `salt[0..16) || tag[0..8) || msg[0..72)` into `d₀`.
2. Calls 1–3 compress `d_{k-1} || msg[64k..64k+64)` directly (`k = 1, 2, 3`),
   producing the leaf digest.

Commitment hashes leaves in place on a zero-gapped heap (`heapOffset s = 32 * (s + s/2)`),
where each sibling pair `(2q, 2q+1)` is followed by a permanent 32-byte zero gap
so parent nodes compress `[96q, 96q+96)` directly without copying or restoring
padding:

- **Salt sampling**: one `RANDOM` call samples `16 * 2^24` bytes (2 cycles/leaf).
- **Leaf loop (32× unrolled)**: 16 sibling pairs per iteration. For each leaf,
  17 instructions copy the 16-byte salt, store the live pointer `x10 = 4072 + 256*i`
  as the 8-byte leaf tag, execute four in-place 96-byte compressions (the fourth
  writing directly to `heap + heapOffset(2^24 + i)`), and advance `x10` by 256.
  With 32 leaves per iteration, loop control costs 3/32 cycles per leaf.
- **Parent loop (32× unrolled + 31-parent tail)**: each parent compresses its
  child pair plus zero gap in 3 instructions (10 cycles), descending 32 parents
  per iteration (`2^19 - 1` iterations) followed by a 31-parent straight-line
  tail down to the root.

The trapdoor stores the zero-gapped heap (`96 * 2^24` bytes) followed by the
16-byte salts (`16 * 2^24` bytes).

- **Batch openings (`k = 128`, level-7 cap table)**: each opened position emits
  its 16-byte salt and 17 lower siblings (`16 + 17 * 32 = 560` bytes/leaf;
  `71,680` bytes for 128 positions), followed by the 128 level-7 internal digests
  `heap[128..255]` (`128 * 32 = 4,096` bytes), totaling `75,776` bytes. The
  checker hashes the 128 cap digests bottom-up in 127 compressions to verify the
  root commitment, then checks each opened leaf 17 levels up against its cap slot
  `cap[index / 2^17]`.
- **Non-batch openings (`k ≠ 128`)**: each opened position emits its 16-byte salt
  and full 24-level authentication path (`16 + 24 * 32 = 784` bytes/leaf).

## Claimed bounds

For a full `2^24`-leaf commitment and a 128-leaf opening:

| Claim | Bound |
| --- | ---: |
| Proof bytes | 75,776 |
| Commitment cycles | 959,447,084 |
| Opening cycles | 40,102 |

- Commitment cycles: `959,447,084` (`338,690,099` steps, `5 * 2^24 - 1 = 83,886,079`
  compression calls).
- Opening cycles: `40,102` (`0` oracle calls).
- Product score: `(959,447,084 + 40,102) * 75,776 = 72,706,101,006,336`.

## Proofs and verification

`programs.json` delivers the three RV64IM images and ABI; `claim.json` declares
the bounds; `Solution.lean` assembles the complete `CommitGolf.Certificate` and
proves equality with `CommitGolf.Artifact.submission`.

- **Execution, completeness, and budgets**: `Commit*.lean`, `Opening*.lean`,
  `Check*.lean`, `CheckCap*.lean`, `LeafRefinement.lean`, `ParentRefinement.lean`,
  `Budgets.lean`, `Machine.lean`.
- **Adaptive binding**: `Binding*.lean` (collision extraction over 4-call tagged
  leaves and 24-level paths, with 120-call cap-tree sibling replay when `k = 128`,
  at most 296 replay / 352 total probe calls).
- **Adaptive statistical hiding**: `HidingTaggedSalt.lean` simultaneously
  reprograms all unopened Call 0 inputs to independent uniform 256-bit digests
  using the injectivity of the 64-bit position tag `leafTag i` alongside the
  128-bit uniform salt (`≤ 3 * q / 2^128 + 6 * N^2 / 2^192`), and
  `HidingHybrid.lean` replaces each unopened leaf coordinatewise under the
  3-block tail chain (`≤ N * 16 * (q + treeBudget + 8) / 2^256`), combining well
  below the `(q + 1) / 2^120` target in `HidingSecurity.lean`.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-96-32-product
```

See [RULES.md](../RULES.md) for the trusted contract and verifier requirements.
