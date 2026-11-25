# commit-golf-96-32-product: 32×16 unrolled in-place gap-heap commit with level-7 cap table

This is a salted binary Merkle commitment over the track's 96→32-byte compression
oracle (`COMPRESSION_INPUT_LENGTH = 768`, 8 cycles per compression call). The programs
use compression only.

## Commitment

Each 2048-bit leaf is absorbed in four 64-byte message blocks starting from a private
32-byte salt (`chaining value (32 bytes) || message block (64 bytes)`), with no padding:
four compression calls per leaf.

Commitment hashes each leaf in place without copying message blocks and stores internal
nodes in a gap-heap layout where every sibling pair `[left | right | 0]` occupies 96
contiguous bytes with a permanent 32-byte zero gap. To amortize loop control overhead
while keeping all memory and immediate offsets nonnegative:

- **32× unrolled leaf loop (`commit-pair`)**: each of the `2^19` iterations processes
  32 leaves as four 8-leaf chunks (`x29 = 2048` advances `x8` after each chunk),
  followed by a 4-instruction loop latch (`1544` cycles per 32 leaves, `48.25`
  cycles/leaf).
- **16× unrolled parent loop (`commit-parent`)**: each of the `2^20 - 1` iterations
  computes 16 internal nodes in descending order using direct 96-byte compression calls
  on the gap heap, followed by a 3-instruction loop latch (`163` cycles per 16 parents,
  `10.1875` cycles/parent) and a 15-node straight-line tail down to the root.

Commitment cycles are exactly `1,047,527,478` (`28` setup + `67,108,865` salt sampling +
`10` ready + `809,500,672` leaf loop + `17` parent setup + `170,917,725` parent loop +
`150` root tail + `11` root copy and halt) with `5 * 2^24 - 1 = 83,886,079` public
queries.

## Level-7 Fixed Cap Table for Batch Openings (`k = 128`)

For scored batch openings (`k = 128` positions), instead of repeating the top 7 Merkle
levels across all 128 authentication paths (`128 * 7 * 32 = 28,672` bytes), the opening
program emits:

1. 128 truncated records of `576` bytes each (`32`-byte salt + `17` lower siblings from
   leaf level `0` up to level `16`, stopping at heap indices `128..255`): `73,728` bytes.
2. The fixed level-7 cap table of all `128` digests at heap indices `128..255` in order:
   `4,096` bytes.

Total batch proof size is `73,728 + 4,096 = 77,824` bytes, and opening cycles are
`40,614`. For non-batch opening counts (`k ≠ 128`), the opening and checker retain the
standard `800 * k`-byte format (`32`-byte salt + `24` siblings per position).

The checker verifies a `k = 128` proof by checking the length (`77,824`), copying the
128 cap digests into a temporary flat heap at scratch `[4608, 8704)`, hashing parents
127 down to 1 into `[544, 4608)` to verify the root against the commitment, and then
running the unified per-position loop for 17 levels against the cap table entry
`cap[index >> 17]` (`127 + 128 * 21 = 2,815` public queries).

## Claimed Bounds (`BATCH = 128`, `LOG_LENGTH = 24`)

| Claim | Bound |
| --- | ---: |
| Proof bytes | 77,824 |
| Commitment cycles | 1,047,527,478 |
| Opening cycles | 40,614 |

The product score is `(commitCycles + openingCycles) * proofBytes = 81,525,939,191,808`.

## Verification

`programs.json` delivers the three machine images and their ABI, `claim.json` states the
claimed metrics, and `Solution.lean` proves the complete `CommitGolf.Certificate`
(admission, termination, completeness, budgets, proof size, prover cycles, adaptive
binding, and hiding) against the generated artifact.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-96-32-product
```

See [RULES.md](../RULES.md) for the trusted contract and verifier requirements.
