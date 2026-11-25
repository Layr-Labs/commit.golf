# commit-golf-96-32-product: in-place 96-byte leaf chain

This is a salted binary Merkle commitment over the track's 96→32-byte compression
oracle. Compression costs eight cycles; forward and inverse permutation calls
cost 30. The programs use compression only.

Each 2048-bit leaf is absorbed in four 64-byte message blocks, starting from a
private 32-byte salt. Every leaf call compresses the full 96-byte input
`chaining value (32 bytes) || message block (64 bytes)` directly, with no
padding: four compression calls per leaf instead of the baseline's eight padded
calls.

Commitment hashes each leaf in place, without copying message blocks. The
32-byte slot just below leaf `i`'s message (free memory for `i = 0`, otherwise
the already consumed last 32 bytes of leaf `i-1`) receives the salt. Call `j`
then compresses the contiguous 96 bytes `[slot+64j, slot+64j+96)`, which hold
the current chaining value followed by message block `j`, and writes the new
chaining value over the last 32 bytes it consumed (`slot+64j+64`). The fourth
call writes the heap leaf slot directly. One leaf costs 25 instructions and 53
cycles: an 8-instruction salt copy, four `(2 pointer setup + ECALL)` calls and a
5-instruction loop latch. The input message memory is overwritten in the
process; it is not part of the trapdoor. The checker keeps the copy-to-scratch
leaf subroutine (scratch bytes 256..351), and both compute the same reference
`leafDigest`.

Parent nodes are unchanged from the baseline: each 64-byte pair of child
digests is padded with 32 zero bytes before calling the 96-byte oracle. The
leaf encoding (fixed 96-byte inputs with the chaining value in the low 256 bits)
is injective, so the collision reduction keeps both inputs. The binding replay
now uses 28 calls per opened record (4 leaf + 24 path), 56 for a claim pair.

The claimed bounds for a full commitment and an opening of 128 leaves are:

| Claim | Bound |
| --- | ---: |
| Proof bytes | 102,400 |
| Commitment cycles | 1,509,949,463 |
| Opening cycles | 48,670 |

Commitment cycles are exactly `90 * 2^24 + 23`: 53 cycles per leaf
(4 compressions of 8 cycles, salt copy, pointers, latch), 33 per internal node,
4 per leaf for salt sampling, plus setup. Commitment makes exactly
`5 * 2^24 - 1` public queries. The opening program and proof layout are
unchanged from the baseline.

The product score is `(commitCycles + openingCycles) * proofBytes`.

`programs.json` delivers the three machine images and their ABI. `Solution.lean`
assembles the complete certificate and proves equality with the generated artifact.
The supporting `CommitGolfCandidate/` modules prove execution, resource bounds,
completeness, binding, and hiding for those images. `Padding96*.lean` covers the
padded parent encoding, temporary memory changes, actual instruction trace, and costs.
The hiding proofs keep the baseline's per-leaf query allowance of eight as an
upper bound; the actual leaf uses four calls.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-96-32-product
```

See [RULES.md](../RULES.md) for the trusted contract and verifier requirements.
