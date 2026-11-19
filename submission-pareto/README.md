# Twelve-bit tile offsets for batched openings

The Pareto claim is **598,194,746 prover cycles and 69,632 proof bytes**. Commitment takes 598,103,075 cycles. Opening 128 positions takes at most 91,671 cycles.

This entry derives from [blocksek’s accepted submission](https://github.com/Layr-Labs/commit.golf/tree/0a65d0acc4bb6c65b57da658bd6383ed4a6e0cf1/submission-pareto), Yukon ID `92dbdd4c-6ef3-4cc9-a393-a464d80540c8`. That construction uses 4,096-leaf tiles, keyed counter-mode salts, two permutation calls per salted leaf and a mixed-width binary Merkle multiproof. Its README records the earlier contributions to that construction.

## Opening program

For each selected index, the opener first finds its position within the tile, then its salt lane modulo 11. The tile size is a power of two. The header constructs the mask 4,095 once, using the tile size already in register x26. The loop retains the mask in x24 for the entire batch.

| Image word | Upstream instruction | Submitted instruction |
|---|---|---|
| 1465 | `addi x5, x0, 0` | `addi x24, x26, -1` |
| 1476 | `remu x28, x6, x26` | `and x28, x6, x24` |

The ABI initializes x5 to zero and the path to the first permutation preserves it. Reusing its redundant header assignment gives the new mask a one-cycle setup in an existing slot. Each selected position now uses a one-cycle AND to extract its tile offset. The four-cycle remainder by 11 still chooses the salt lane. A nonempty opening of size *u* saves exactly 3*u* cycles. The empty opening takes seven cycles. The 128-position saving is 384 cycles.

Sections 5 and 7.1 of *Faster Merkle Commitments with T8 Leaves* by Thomas Coratger, Giacomo Fenzi and Eylon Yogev distinguish per-record work from shared authentication paths and examine packing overhead across a batch. Here the per-record optimization targets salt addressing in the challenge’s existing two-permutation construction. The commitment, checker, queries and transmitted multiproof retain the upstream construction.

## Certificate and reproduction

[programs.json](programs.json) contains the three RV64 images and the ABI. [claim.json](claim.json) records the bounds. [Solution.lean](Solution.lean) links the certificate to the delivered images. [P4OpenLoop.lean](CommitGolfCandidate/P4OpenLoop.lean) proves bit-mask equivalence and the cost of the revised loop. [P4OpenHeader.lean](CommitGolfCandidate/P4OpenHeader.lean) establishes the mask and selector at entry. [P4OpenFull.lean](CommitGolfCandidate/P4OpenFull.lean) proves the complete opening bound.

Run `yukon setup --track pareto` and `yukon run --track pareto` from the benchmark checkout on a supported Linux host.

An independent interpreter compared both opening images using the same sparse trapdoor and permutation. Empty, boundary, contiguous, scattered and random batches produced identical proof bytes and permutation requests. The positions `i * 131072` for `0 ≤ i < 128` reached both claimed opening bounds. The opening image differs in two words. The commitment and checker images are byte-identical to the direct predecessor.
