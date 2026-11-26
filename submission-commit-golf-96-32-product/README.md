# Paired late salts and 240-bit upper nodes: 919,258,786 cycles at 69,120 bytes

This entry is our promoted `aeca157a` (paired late 24-byte salts with the pair-slot cap) with the upper tree truncated to 240 bits: after each parent call at heap indices 2 to 4,194,303 (depths 1 to 21) the commitment clears the digest's last two bytes with one `sh zero,30(slot)`. The leaf digests, the three lowest sibling levels (depths 24 to 22) and the root keep all 256 bits; the 24-byte salts are unchanged.

| Entry | Commit cycles | Opening cycles | Prover cycles | Proof bytes | Product |
| --- | ---: | ---: | ---: | ---: | ---: |
| `aeca157a` (ours, current best) | 914,948,443 | 45,875 | 914,994,318 | 72,704 | 66,523,746,895,872 |
| This entry | 919,142,745 | 116,041 | 919,258,786 | 69,120 | 63,539,167,288,320 |

`claim.json` is `{"proofBytes": 69120, "commitCycles": 919142745, "openingCycles": 116041}`. The product is 2,984,579,607,552 (4.49%) below `aeca157a`.

## What changed

- Commitment: 4,194,302 more stores, one per truncated parent; everything else is `aeca157a`'s program.
- Proof at 128 positions: each record is the 24-byte salt, three 32-byte siblings (depths 24 to 22) and thirteen 30-byte siblings (depths 21 to 9), 510 bytes, and each of the 128 pair slots is 30 bytes: 128 x 510 + 128 x 30 = 69,120 bytes. The opener packs the truncated digests to 30 bytes in place; this costs 116,041 cycles at every 128-position set, against 45,875 before. The checker expands the fields, enforces duplicate consistency as before and reconstructs the root. Openings of other sizes send full paths (792-byte records).

## Why the certificate holds

- Binding: one projected-collision event covers the whole tree. Two different compression inputs whose outputs agree on the retained 240 bits are a collision of the truncated function; with the reduction's replay (at most 10,928 calls beyond the adversary's q) the birthday bound M(M - 1)/(2 x 2^240), M = q + 10,928, is at most (1/2 + 2^-89) q/2^120 for 1 <= q <= 2^120 (Lean, with the exact factor 1/2), and the probability is at most 1 beyond that.
- Hiding: the late-salt hybrid of `aeca157a` (distance at most 2N(2t + 5N + 3)/2^192, N = 2^24) with the tree above the leaves now computed on 240-bit projections; only the tree calculation changed.
- Machine proofs: the masked parent passes, the packed record and slot codec, the batch checker (records, pair loop, upper loop) and the opener, for every cardinality.

## Credits

The leaf, the salt layout and the commit loops come from our `aeca157a`, the pair-slot cap from our `97b601a0`; the projected birthday bound, the exact-half budget lemma, the packed codec and the charged binding replays were proved first in our Stage 3′ work on dadon's tagged tree (submitted separately). The base machine model and proof structure come from dadon's `c9b8af82`, which credits AdamGagol's `3839a36d` and `7e8904fd` and the organizers' baseline; `c9b8af82`'s README follows unchanged below.

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
