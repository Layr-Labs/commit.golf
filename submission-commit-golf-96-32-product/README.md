# Paired 24-byte late salts: 914,994,318 cycles at 72,704 bytes

This entry changes the leaf hash of the 96-32 leaders so that the salt enters only the last of the four compression calls, and lays out the leaves in pairs so that one 48-byte `RANDOM` call writes the salts of an even and an odd leaf exactly where their last calls read them. No salt is copied and no position tag is stored. The tree, the pair-slot cap of our `97b601a0` and the proof format otherwise stay as they were.

| Entry | Commit cycles | Opening cycles | Prover cycles | Proof bytes | Product |
| --- | ---: | ---: | ---: | ---: | ---: |
| `3e63809d` (dadon) | 959,447,084 | 40,102 | 959,487,186 | 75,776 | 72,706,101,006,336 |
| `97b601a0` (ours, current best) | 959,447,084 | 40,631 | 959,487,715 | 71,680 | 68,776,079,411,200 |
| This entry | 914,948,443 | 45,875 | 914,994,318 | 72,704 | 66,523,746,895,872 |

`claim.json` is `{"proofBytes": 72704, "commitCycles": 914948443, "openingCycles": 45875}`. The product is 2,252,332,515,328 (3.27%) below `97b601a0`.

## The leaf

For a 256-byte leaf m and a private 24-byte salt s:

    u = C(m[0..96]),   a = C(u || m[96..160]),   b = C(m[160..256])
    even leaf digest = C(a || b || 0^8 || s),   odd leaf digest = C(s || 0^8 || a || b)

where C is the track's 96-to-32-byte compression. That is four calls per leaf, as in `c9b8af82` and `3e63809d`, but the salt is not in the first call. The final-call rows of leaves 2j and 2j+1 are consecutive, so the 24 salt bytes of the even row and the 24 of the odd row are adjacent, and one 48-byte `RANDOM` per pair fills both (8,388,608 draws). Salt sampling and placement cost about 4 cycles per leaf, against 7 in `3e63809d` (16-byte copy, tag store, and its share of one bulk draw). The commitment makes 5 x 2^24 - 1 = 83,886,079 compression calls, as before.

The parents are the gap-heap binary parents C(left || right || 0^32) with full 256-bit digests. At 128 positions the proof is `97b601a0`'s pair-slot format with 24-byte salts: 128 records of 24 + 16 x 32 = 536 bytes and 128 pair slots of 32 bytes, 72,704 bytes; openings of other sizes send full paths. Every 128-position opening takes exactly 45,875 cycles and makes no oracle calls; the batch checker makes at most 2,815 calls (2,560 for the records, at most 128 for touched pairs, 127 for the upper tree).

## Why the certificate holds

- Hiding: `CommitGolfCandidate.Late.late_hiding` proves the contract's statistical hiding statement for this scheme with distance at most 2N(2t + 5N + 3)/2^192 (N = 2^24), that is t x 2^-166 + 2^-140.7, below (t + 1)/2^120. A hidden leaf's digest is a fresh output unless a query hits its final input, which needs its 192-bit salt; the proof models the honest computation as a single pass of at most 5N calls and shows that the 2^23 48-byte draws of the sampling loop equal one uniform salt tape. With 24-byte salts no position tag is needed.
- Binding: two accepted openings that disagree at a position are reduced to a compression collision. The leaf's orientation (salt first or last) is fixed by the position's parity, so equal final inputs force equal (a, b), and equal branch replies force equal message ranges [0, 96), [96, 160) and [160, 256). The reduction replays the two records with at most 10,872 calls and 56 further probes.
- Machine proofs: the commit proof composes the paired salt-sampling loop, the leaf-hashing loop and the 24 parent passes and identifies the root and the retained trapdoor; the opener's proof covers every cardinality; `PairCap.batchEvaluation` proves the batch checker's termination, query bound and exact acceptance condition for every correctly sized input, including malicious bytes.

## Credits

The base machine and proofs come from dadon's `c9b8af82`, which credits AdamGagol's `3839a36d` and `7e8904fd` and the organizers' baseline; the pair-slot cap and its checker proofs come from our `97b601a0` (built on dadon's `3e63809d`). The hiding proof adapts `c9b8af82`'s fixed-oracle simulation and coordinate hybrid. `c9b8af82`'s README follows unchanged below; its figures describe that entry.

---

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
