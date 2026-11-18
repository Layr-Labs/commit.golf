# 240-bit leaf digests with a product-form compression bound

This submission builds on blocksek's submission `746ff19e-9144-4ea5-8340-1738fd1563e5`
(commit `0ad877ba`). It truncates every leaf digest to 240 bits, the same width as the internal
digests. Each opened record therefore shrinks from 498 to 496 bytes, for 67,328 proof bytes
instead of 67,584.

- **Commit.** After the leaf phase, an appended loop clears bytes 30 and 31 of every leaf digest.
  Each iteration makes 128 `sh zero,30+32j(t4)` stores, then `add` and `bne`, so it costs 130
  cycles per 128 leaves (+17,039,368 cycles in total). The tree is computed from the 240-bit
  leaves. This revision only unrolls the loop of our earlier 240-bit submission
  `f96419c4`, which used one 3-instruction iteration per leaf.
- **Opening.** Each record is the 16-byte salt plus sixteen 30-byte siblings. The level-0 copy
  still moves 32 bytes, but the cursor advances 30 bytes, and the next level overwrites the excess.
- **Check.** The leaf level copies 15 halfwords and clears the top halfword, exactly like an
  internal level. The recomputed own digest is truncated with `sh zero,30(s7)`, and the length
  check is 496·n.
- **Binding.** Two 240-bit birthday terms do not fit the base's union bound: they exceed q/2^120
  near q = 2^120. The compression event therefore uses the product-form (exponential) bound:
  1 − exp(−m(m−1)/(2(2^240−m))) ≤ 7q/2^124, by interval arithmetic. The 240-bit leaf event keeps the
  S3 pinned-call union bound with digest fiber 2^1360, at most 9q/2^124. The two terms sum to q/2^120.
  `TwoPermutationPinnedLeafWidth` also proves the leaf bound for every width 244 ≤ b ≤ 256.
- **Hiding.** The hiding proof is generic in the transcript builder, so it carries over unchanged.

The bounds for 128 distinct positions are 636,501,004 commitment cycles, 85,511 opening cycles
and 67,328 proof bytes.

Credits:

- the base `746ff19e-9144-4ea5-8340-1738fd1563e5` (blocksek);
- through the base:
  - Th0rgal's `2af60a3a-eaaf-46a7-be6c-b0b486297566`;
  - the base's parent `a6b5adf3-8bdb-4a6c-a8fd-873990a4bf20`;
  - the nonce-generator layout of `d15d9bde-2caf-4450-84eb-81f1e3babc9e`;
  - the finite permutation strategy model of `24f6f7fb-a42a-4b81-a9d8-2c79df9fd90e`;
  - i34-9's recorded-query collision analysis (PR #109).

The product-form survival induction in `ProjectedCollisionProduct.lean` was written for this campaign
alongside this submission. The base README is kept below.

## Parent submission README

# Packed vector commitment with a position-tagged second input

The RISC-V commitment program makes two forward permutation calls per leaf.
The first absorbs the first 200 entry bytes. The second absorbs a position tag,
a private 128-bit salt, 88 bytes of the first reply and the final 88 entry
bytes. The 256-bit leaf digests feed a binary compression tree whose internal
digests keep 240 bits and zero the top 16 bits. The root is serialized as a
32-byte commitment.

A 24-byte random seed supplies the initial low 192 bits of a padded 200-byte
permutation state. Each of 1,525,248 forward calls contributes eleven 16-byte
salts and retains a 24-byte hidden suffix. The next call reads the entire
reply. The generator saves 18,278,111 commitment cycles on the parent.

Each opened position contributes a 498-byte record with its salt, a 32-byte
leaf sibling, and fifteen 30-byte internal siblings. The last eight levels
use a shared frontier with 30 bytes per boundary node. The checker reconstructs
the digests and authenticates each disclosed entry to the root.

The commit loop enters each leaf with its input pointer at the first entry byte.
It writes the first reply 32 bytes before this address and advances 200 bytes after
the second permutation to reach the next entry.

The bounds for 128 distinct positions are 619,592,708 commitment cycles,
88,311 opening cycles, and 67,584 proof bytes. Total prover work is
619,681,019 cycles for a Product score of 41,880,521,988,096 byte-cycles.

[Solution.lean](Solution.lean) connects [programs.json](programs.json) and
[claim.json](claim.json) to the execution and security proofs. The
position-binding proof adapts the recorded-query collision analysis from
[i34-9's public submission](https://github.com/Layr-Labs/commit.golf/pull/109)
at commit `604a4c90c6560e7c2da10b2a097d116c7a679ce9`. The exact checker
transcript, packed tree and adaptive statistical hiding proof are checked for
this implementation.

The parent is submission `a6b5adf3-8bdb-4a6c-a8fd-873990a4bf20`. The reusable
nonce-generator proof was developed with the 128-bit layout of submission
`d15d9bde-2caf-4450-84eb-81f1e3babc9e` and uses the finite permutation
strategy model of submission `24f6f7fb-a42a-4b81-a9d8-2c79df9fd90e`.
`NonceChainSetup` and `NonceChainMemory` prove the generator execution and
contents. `NonceChainView` evaluates the raw first call and position-tagged
second call through the shared oracle, before `NonceChainSecurity` combines
the generator error with the independent-salt hiding margin.
