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
