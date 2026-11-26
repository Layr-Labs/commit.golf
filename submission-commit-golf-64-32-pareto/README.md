# 59c9d775 on the 64-32 track: 1,427,720,065 cycles at 67,072 bytes

This entry is parithosh's accepted Pareto entry `59c9d775` (blocksek's `746ff19e` packed two-permutation tree with 238-bit internal digests under a product-form birthday bound and a packed proof stream), re-certified for `commit-golf-64-32-pareto`, where a forward or inverse permutation call costs 30 cycles instead of 8. The three programs, the proof format and every proof byte are unchanged. Only the claim and the Lean proofs whose statements carried the 8-cycle price change.

| | `59c9d775` on `pareto` | This entry |
| --- | ---: | ---: |
| Commit cycles | 653,016,525 | 1,424,769,485 |
| Opening cycles | 2,950,580 | 2,950,580 |
| Prover cycles | 655,967,105 | 1,427,720,065 |
| Proof bytes | 67,072 | 67,072 |

`claim.json` is `{"commitCycles": 1424769485, "openingCycles": 2950580, "proofBytes": 67072}`. The commitment makes 35,079,680 permutation calls (two per leaf and 1,525,248 in the nonce chain) and 16,777,215 compression calls, so its bound grows by exactly 22 x 35,079,680 = 771,752,960. The opening makes no permutation calls and its bound is unchanged.

## What changed in the proofs

Every permutation call reaches the proofs through `execute_permutation_call` (`TwoPermutationSyscall`) and `Chain.chain_perm_call` (`NonceChainSyscall`); both now charge 30. Each block that contains a permutation call grows by 22 per call, fixed where its constant is first stated: a leaf costs 69 cycles instead of 25 (a tile of 4,096 leaves 282,674 instead of 102,450), a nonce-chain call 32 instead of 10 (the nonce setup after the seed draw 48,831,784 instead of 15,276,328), the checker's leaf 72 instead of 28. The packed checker's record leaf block stated its cost as 41 instructions plus 7 x 2 permutation calls (55 cycles); it is now 41 + 29 x 2 = 99. `Execution.lean` carries the organizers' 30-cycle form of the generic cost lemma (`oracleCycles_le_thirty`). The prototype commit modules still in the import closure follow the same rule; compression calls stay at 8.

Changed: `Execution`, `NonceChainExec`, `NonceChainLoop`, `NonceChainSetup`, `NonceChainSyscall`, `TwoPermutationAllLeaves`, `TwoPermutationCheckRecord`, `TwoPermutationCheckerLeafRun`, `TwoPermutationCommitRun`, `TwoPermutationFixedDraw`, `TwoPermutationLeafGroup`, `TwoPermutationLeafRun`, `TwoPermutationPackedAssembly`, `TwoPermutationPackedCommit`, `TwoPermutationPackedLeafGroups`, `TwoPermutationPackedLeafLatch`, `TwoPermutationPackedLeafRun`, `TwoPermutationPackedMeaning`, `TwoPermutationPackedRecordLeafBlock`, `TwoPermutationPackedRecordLeafCalls`, `TwoPermutationPackedRecordLeafPhysical`, `TwoPermutationSyscall`, plus `Solution.lean` and `claim.json`. Every other file, `programs.json` included, is byte-identical to `59c9d775`, except this README, which adds the header above its original text.

## Credits

The construction, programs and proofs are parithosh's `59c9d775`, built on blocksek's `746ff19e` (which credits Th0rgal's `2af60a3a` and kaankolcu's `a6b5adf3`); its README is kept below. Only the repricing is ours.

---

# 238-bit internal digests with a packed proof stream

This submission builds on submission `746ff19e-9144-4ea5-8340-1738fd1563e5`
(blocksek, commit 0ad877ba). It keeps that base's commitment scheme and changes
two things: internal tree digests keep 238 bits instead of 240, and the
delivered opening proof is packed so that each internal digest costs 29.75
bytes instead of 30.

Certified bounds for 128 distinct positions: 653,016,525 commitment cycles,
2,950,580 opening cycles and 67,072 proof bytes (base: 619,461,636 /
85,511 / 67,584).

## Binding at 238 bits

With 240-bit digests, the base bounds compression collisions with the union
birthday sum m(m-1)/2^241. At 239 bits or fewer, that sum is above the target
q/2^120 for budgets just below 2^120. The paid replay allowance (m ≤ q+2^31)
and the leaf term make the gap wider.
[ProjectedCollisionProduct.lean](CommitGolfCandidate/ProjectedCollisionProduct.lean)
proves a product-form bound by the same adaptive lazy-sampling induction:
Pr[low-w collision] ≤ 1 - ∏_{i<m}(1 - i/2^w). It then shows
1 - ∏ ≥ exp(-m(m-1)/(2(2^w-m))) and closes 15q/2^124 for w = 238 and 239
using a rational grid of (1-u/64)^64 checks.
[ProjectedCollisionROM.lean](CommitGolfCandidate/ProjectedCollisionROM.lean)
redefines the stored projection as 0#2 ++ low238. The pinned leaf event is
tightened from q/2^122 to q/2^124 (it had about 2^-10 slack), so the split is
15q/2^124 + q/2^124 = q/2^120.

## Commit and checker masks

Each unrolled commit parent is now six words: ECALL; LD x31,24(x12);
AND x31,x31,x30; SD; two pointer decrements. That is two cycles more per
internal node, for 2^24 - 1 nodes. A three-word prelude loads the mask
2^46 - 1 into x30, and the unroll is 28,679 parents × 585 groups, so the
latch, root copy and nonce chain keep their word positions. Both checker parent
hash sites jump to small out-of-line stubs that clear the top 18 reply bits.

## Packed proof format

[ProofCodec.lean](CommitGolfCandidate/ProofCodec.lean) defines the format.
Record heads (salt and leaf sibling, 48 bytes) are copied unchanged. Each
30-byte internal digest keeps its first 29 bytes, and the six live bits of
its byte 29 go to a remainder block at the end, four digests per three
bytes. The worst case is 48·128 + 29·2048 + 3·512 = 67,072 bytes. The
opening image ends with an in-place forward pack pass
([TwoPermutationPackedOpeningPack.lean](CommitGolfCandidate/TwoPermutationPackedOpeningPack.lean)).
The checker image starts with an in-place backward unpack pass that rejects
malformed lengths and restores the old 498/30-byte layout, after which the
unchanged checker runs (`TwoPermutationPackedUnpack*.lean`).
[HonestCodec.lean](CommitGolfCandidate/HonestCodec.lean) proves that every
honest proof round-trips. Hiding is unchanged: `scheme_hiding_of_chain` is
generic in the transcript builder, and the new builder packs the old
transcript. The x16 position count at the pack pass comes from a generic
register-preservation theorem
([RegisterPreservation.lean](CommitGolfCandidate/RegisterPreservation.lean)).

## Credits

- Base: `746ff19e-9144-4ea5-8340-1738fd1563e5` (blocksek). Everything not
  listed above is theirs, including the packed tree, nonce generator, hiding
  and checker proofs.
- The base's own credits carry over: parent `a6b5adf3-8bdb-4a6c-a8fd-873990a4bf20`,
  nonce generator from `d15d9bde-2caf-4450-84eb-81f1e3babc9e`, permutation
  strategy model from `24f6f7fb-a42a-4b81-a9d8-2c79df9fd90e`, and the
  recorded-query collision analysis from i34-9's public submission (PR 109,
  commit 604a4c90c6560e7c2da10b2a097d116c7a679ce9).

---

Base README follows.

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
