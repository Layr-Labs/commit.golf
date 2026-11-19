# 243-bit leaves and six-bit record heads

This work builds on the locally verified 66,800-byte milestone `ae0f257`,
which starts from parithosh's submission
`5b22c857-2c19-4975-8b87-e730b92c1efa` (commit
`c1e4e5347a401931539e5df5a234c6367365124d`). Its credits and ancestry
are retained below.

The claim is **66,784 proof bytes**, **756,825,559 commitment cycles** and
**4,064,963 opening cycles**. Internal digests remain 238 bits, leaves are
243 bits, salts remain 123 bits, and binding and hiding target 120 bits.
Commit keeps the low 51 bits of each leaf's top doubleword. The checker
uses matching 13-bit shifts to truncate its computed leaf.

`HeadStreamCodec.lean` keeps 45 complete head bytes and 29-byte digest bodies
in each main record. The remaining six live salt/leaf head bits follow the
digest-remainder stream, four heads per three bytes. The final partial group
is zero-padded. At the scored maximum each record and its remainder bits
occupy 3,936 bits, and there are 128 cap digests of 238 bits each:
`128 * (3936 + 238) / 8 = 66,784` bytes.

The opener conversion pass has execution, byte-frame and exact cycle proofs.
Unused unrolled slots are retained to preserve instruction addresses. The
opening certificate establishes the exact serialized transcript and the
scored cycle and size bounds. Its full-position-set fuel is `2^39`.

`HeadStreamRestore.lean` proves the inverse conversion, including honest
round trips and empty/missing-record cases. The checker has a 73-instruction
restoration pass followed by the existing unpacker and checker. Oversized
virtual lengths and incomplete records are rejected before proof-memory
accesses. Origin-parameterized memory preserves unaligned-word semantics;
register preservation uses abstract loader outputs without expanding the
concrete memory image. Checker fuel remains `2^40`.

`Leaf243CombinedMargin.lean` proves the combined internal product bound
and `pinnedWidthTerm 243` fit `q/2^120` throughout the nontrivial budget
range, using rational interval bounds on the exponential. Larger budgets
use the probability cap. `Leaf243ReplayProbability.lean` applies this
combined margin to the actual recorded-query collision events, rather
than retaining the inherited 15/16 + 1/16 allocation.

The manifest carries the exact certified machine images. Official verification
results are reported separately, not inferred from a build.

## Inherited 245-bit baseline notes and credits

The following notes describe the inherited 66,816-byte submission.

### 238-bit internal digests with a packed proof stream

This submission builds directly on submission
`59c9d775-9e87-4aee-baf4-132a0c9df730` (238-bit internal digests and a packed
proof stream, 67,072 bytes), which itself builds on
`746ff19e-9144-4ea5-8340-1738fd1563e5` (blocksek, commit 0ad877ba). It keeps that base's commitment scheme and changes
four things: internal tree digests keep 238 bits instead of 240, leaf digests
keep 245 bits instead of 256, honest salts carry 123 uniform bits (merged from
the B2 change, see below), and the delivered opening proof is packed so that
each internal digest costs 29.75 bytes instead of 30 and each record head 46
bytes instead of 48.

Certified bounds for 128 distinct positions: 756,825,559 commitment cycles,
3,124,668 opening cycles and 66,816 proof bytes (base: 619,461,636 /
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
A record head (16 salt bytes, 32 leaf-sibling bytes) becomes 46 bytes: salt
byte 15 (three live bits) and leaf-sibling byte 30 (five live bits) share one
byte and leaf-sibling byte 31 (always zero) is dropped. Each 30-byte internal
digest keeps its first 29 bytes, and the six live bits of its byte 29 go to a
remainder block at the end, four digests per three bytes. The worst case is
46·128 + 29·2048 + 3·512 = 66,816 bytes. The
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

## 123-bit salts (B2, merged)

After the counter-mode expansion, a 50-instruction loop runs 2^20 times over
the salt array and clears bits 59..63 of the high word of each of the 2^24
salts. The pass sits at the end of the commit image (words 233324..233379),
replaces the expansion's return jump, and costs 52,428,805 commitment cycles.
Every honest salt in the trapdoor and in an opening satisfies
`s.extractLsb' 123 5 = 0` (`ChainRepresentation.nonce`:
`trapdoorSalt … = maskedNonces …`, with `maskedNonces π k i = maskSalt
(actualNonces π k i)`). The checker still reads 16 salt bytes and accepts any
salt. The hiding hit rates become 1/2^123 per query, the reference game bound
becomes 7(t+1)/2^123 (`pinned_final_hiding_margin`), and the total still fits
min(1, (t+1)/2^120) (`chain_budget`). Proof changes: `NonceChainMask` (new),
`NonceChainSetup`, `NonceChainMemory`, `NonceChainLayout`, `NonceChainSecurity`,
`NonceChainRepresentation`, `TwoPermutationHidingHits`, `TaggedPinned*`,
`TwoPermutationPinned*` and the cycle constants.

## 245-bit leaf digests

After the leaf phase, commit word 45128 jumps to a pass appended at words
233380..233482 that ANDs the top doubleword of every leaf digest with 2^53 - 1
(32 leaves per iteration, 2^19 iterations, 51,380,229 extra cycles) and then
returns to the parent setup. The reference heap stores
`projectLeaf true d = d mod 2^245` at the leaves
([TwoPermutationTranscript.lean](CommitGolfCandidate/TwoPermutationTranscript.lean));
`pinnedFullLeafDigests` stays 256-bit, so hiding is unchanged. The checker's
first lower-setup instruction (word 58) jumps to a stub at words 542..547 that
clears the top 11 bits of its own leaf digest before the leaf level
([TwoPermutationPackedLeafTrunc.lean](CommitGolfCandidate/TwoPermutationPackedLeafTrunc.lean)),
so no checker PC moves. The leaf binding event compares 245-bit digests;
the width-generic pinned bound
([TwoPermutationPinnedLeafWidth.lean](CommitGolfCandidate/TwoPermutationPinnedLeafWidth.lean),
from B1) still gives q/2^124 for b ≥ 244, so the split stays
15q/2^124 + q/2^124. The 123-bit salts and 245-bit leaves are what make the
46-byte heads round-trip: `HonestCodec.head_facts_of_small_salts` and
`PackedCertificate.honest_head_facts`.

## Credits

- Direct base: `59c9d775-9e87-4aee-baf4-132a0c9df730` (238-bit internal
  digests, product-form birthday bound, packed proof codec and wrappers).
- Underlying base: `746ff19e-9144-4ea5-8340-1738fd1563e5` (blocksek). Everything
  not listed above is theirs, including the packed tree, nonce generator,
  hiding and checker proofs.
- The 123-bit salt change (commit mask pass and hiding constants) is unsubmitted
  work by a teammate (B2), developed on the same base and merged here.
- The width-generic pinned leaf bound (`TwoPermutationPinnedLeafWidth.lean`) and
  the leaf truncation approach come from a teammate's (B1) leaf-width work.
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
