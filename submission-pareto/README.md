# One full-width parent level with the centered heap pointer

This tree is 3362757c-d12b-4f9d-a2d3-c6f49c8865e6 (one full-width parent level on the mixed-width chained-salt
tree) with the leaf loop of 58441773-f004-456d-be19-a0286db9356c, which carries the centered heap pointer of
746ff19e-9144-4ea5-8340-1738fd1563e5. Nothing else changes: the tree, the salts, the opening and check programs,
the record layout and the proof size are 3362757c's.

**Commit image.** Words 0-45,132 are 58441773's (prologue and leaf loop). The two former `nop` slots after the
generator returns bias the digest pointer `s4` and the group-end sentinel `t3` by 2,048, so digests are written at
`-2048 + 32·(slot mod 128)`; the 64 `addi s4,a2,32` rebases per 4,096-leaf body become 32 `add s4,s4,t2`. The salt
pointer `s6` was already centered in 3362757c and is unchanged. Words 45,133-233,125 are 3362757c's words
45,165-233,157 moved down by 32 (stop setup `lui x17,65536`, full-width phase of 256 groups of 32,768 parents,
projected phase of 178,481 groups of 47 parents, latch, root copy, padding); every branch and jump in that range is
PC-relative and both ends move together, so the words are unchanged. The salt generator block starts at word
233,126 with 58441773's re-encoded return jump. The image has 233,325 words.

**Bounds.** Commit cycles 611,560,862 - 131,072 = **611,429,790** (51,856,895 oracle calls, unchanged); opening
**88,567** and proof bytes **67,840** (3362757c's, unchanged). `claim.json`:
`{"commitCycles": 611429790, "openingCycles": 88567, "proofBytes": 67840}`.

**Proofs.** 457 of the 475 candidate modules are byte-identical to 3362757c. The 13 leaf-loop and generator modules
(`NonceChainExec/Loop/Setup`, `MixedWidthStopRun`, `TwoPermutationPackedSetup`, `TwoPermutationPackedLeaf*`) are
58441773's, byte for byte. The five modules both entries changed (`MixedWidthParentImage`, `MixedWidthParentMeaning`,
`TwoPermutationPackedCommit`, `TwoPermutationPackedAssembly`, `TwoPermutationPackedMeaning`) and `Solution.lean` are
3362757c's with every post-leaf word index moved by -32, every post-leaf PC by -128 and every leaf-phase step and cycle
total by -131,072; in `MixedWidthParentImage` the full-width window phases are recomputed for the shift
(32 = 2 mod 3) and the decode lemmas are 58441773's.

## Base tree (3362757c)

# One full-width parent level (Pareto variant of the mixed-width chained-salt tree)

This candidate is the tree described below with the width threshold moved down by one level: only the
bottom internal level (nodes 2^23 .. 2^24 - 1) keeps all 256 bits, higher internal levels keep 240 bits.
The full-width parent phase runs 256 groups of 32,768 parents and stops at node 2^23 - 1; the projected
phase runs 178,481 groups of 47 parents. Records carry two 32-byte and fourteen 30-byte siblings
(500 bytes). Claimed bounds: 67,840 proof bytes, 611,560,862 commitment cycles, 88,567 opening cycles.

## Base tree (two full-width levels)

# Mixed-width vector commitment with chained salts

The RISC-V commitment program makes two forward permutation calls per leaf.
The first absorbs the first 200 entry bytes. The second absorbs a position tag,
a private 128-bit salt, 88 bytes of the first reply and the final 88 entry
bytes. The 256-bit leaf digests feed a binary compression tree. Its bottom
two internal levels retain all 256 bits; higher internal levels keep 240 bits
and zero the top 16 bits. The root is serialized as a 32-byte commitment.

A 24-byte random seed supplies the initial low 192 bits of a padded 200-byte
permutation state. Each of 1,525,248 forward calls contributes eleven 16-byte
salts and retains a 24-byte hidden suffix. The next call reads the entire
reply. The generator saves 18,278,111 commitment cycles on the parent.

Each opened position contributes a 502-byte record with its salt, three
32-byte siblings, and thirteen 30-byte internal siblings. The last eight levels
use a shared frontier with 30 bytes per boundary node. The checker reconstructs
the digests and authenticates each disclosed entry to the root.

The commit loop enters each leaf with its input pointer at the first entry byte.
It writes the first reply 32 bytes before this address and advances 200 bytes after
the second permutation to reach the next entry.

The claimed bounds for 128 distinct positions are 607,010,386 commitment
cycles, 88,823 opening cycles, and 68,096 proof bytes. Total prover work is
607,099,209 cycles for a Product score of 41,301,027,736,064 byte-cycles.
Release validation requires a clean run of the original verifier against the
exact submitted artifact. Targeted module compilation alone is insufficient;
the submission note records the release validation evidence.

The mixed parent loop removes 12,582,912 high-bit mask instructions. The
changed loop setup and latches add 590 cycles, giving a net commitment
saving of 12,582,322 cycles against the chained-salt parent. Opening work
and the certified proof bound each increase by 512. The machine image keeps
the original salt-generator entry and return addresses; unreachable padding
separates the mixed tree's terminating instruction from the generator code.

[Solution.lean](Solution.lean) connects [programs.json](programs.json) and
[claim.json](claim.json) to the execution and security proofs. The
position-binding proof adapts the recorded-query collision analysis from
[i34-9's public submission](https://github.com/Layr-Labs/commit.golf/pull/109)
at commit `604a4c90c6560e7c2da10b2a097d116c7a679ce9`. The exact checker
transcript, mixed tree and adaptive statistical hiding proof are the subjects
of the candidate's integration checks.

The direct chained-salt parent is submission
`c28dd9ca-eec2-4c63-a1d2-3fe14c5e5492`. Its predecessor includes submission
`a6b5adf3-8bdb-4a6c-a8fd-873990a4bf20`. The mixed-width work also uses the raw
leaf implementation and proofs from submission
`33bdbed6-b605-43fc-b808-348ea3c87e3b`. The mixed-width implementation was
developed from the packed 240-bit tree and its native proof machinery in
submission `2e9939e5-492f-415b-b2c1-6c87d959b79a` (source `a18d0e6`). This is
material implementation reuse, not only a score comparison. The reusable
nonce-generator proof was developed with the 128-bit layout of submission
`d15d9bde-2caf-4450-84eb-81f1e3babc9e` and uses the finite permutation
strategy model of submission `24f6f7fb-a42a-4b81-a9d8-2c79df9fd90e`.
`NonceChainSetup` and `NonceChainMemory` prove the generator execution and
contents. `NonceChainView` evaluates the raw first call and position-tagged
second call through the shared oracle, before `NonceChainSecurity` combines
the generator error with the independent-salt hiding margin.
