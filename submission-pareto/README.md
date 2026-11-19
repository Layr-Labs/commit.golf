# 238-bit leaves, 122-bit salts and no record-head stream

This candidate branches from the verified 66,736-byte commit
`95e2306200ce78bfab74b69afe593ba24492521b`.
It targets **66,688 proof bytes**, **756,825,559 commitment cycles** and
**4,065,542 opening cycles**. Binding and hiding target 120 bits. Official
verification results are reported separately, not inferred from a build.

## Minimum width and binding margin

The minimum width under the current adaptive joint-survival reduction with at
least 2% numerical margin is **238**. The normalized maximum is
`0.9025124681566164` (9.74875% margin); width 237 gives
`1.276345372677903` and fails. Smaller widths only increase this envelope.

The width-238 fiber instantiation retains the exact forward bound
`2^1362 + 2^897`, rather than rounding it up to the next power of two.
Its finite conditional hazard still fits `(known+1)/2^238`; the extra virtual
slot absorbs the small fiber and depleted-permutation corrections.
`JointOracle238*` tracks compression and forward/inverse permutation queries
jointly, charging each adaptive query only to its own oracle.
`Leaf238JointMargin.lean` proves an explicit 2% reserve for positive budgets
below `2^120`, including replay overhead. That theorem is used by
`JointOracle238Probability.lean`; `Leaf238ReplayProbability.lean` connects the
bound to the recorded executable replay, with probability capping for large
budgets. The generic `PinCallFibers` and `PinCallNatCounts` proofs avoid
expanding the encoding or passing through real-valued cardinalities.

## Exact proof layout

The 122 salt bits and 238 leaf bits occupy exactly 45 bytes, with the two salt
head bits in the upper bits of the leaf's last byte. There is **no separate
record-head stream**. Each internal digest still occupies 238 bits:
29 body bytes and six bits in the digest-remainder stream.

At the scored maximum there are 128 records with fifteen internal siblings
each, plus 128 cap digests:
`128*(122+238+16*238)/8 = 66688` bytes.
Equivalently, `45*128 + 29*2048 + 1536 = 66688`.
The spread-position case attains these node counts. This saves exactly
**48 bytes** over `95e2306`, including the transition through zero head bits.

`HeadStreamZero.lean` proves inverse conversion, honest round trips, the
maximum size, empty-input and missing-record cases.
The native opener merges each salt head into the last leaf byte.
The 78-instruction checker restoration pass extracts those salt bits, clears
them from the leaf byte, restores the intermediate head byte and composes
with the existing unpacker. Capacity and incomplete-record guards reject
before proof-memory accesses. Origin-parameterized memory preserves unaligned
word semantics; register preservation uses abstract loader outputs.
Opening fuel remains `2^39` and checker fuel remains `2^40`.

Commit keeps 46 bits of each leaf's top doubleword. The checker uses matching
18-bit shifts. The transcript projection, honest codec, executable checker,
opening serialization and certificate use the same 238-bit leaf width.
The manifest carries the exact certified machine images.

## Split-budget hiding at 122 bits

The hiding construction is unchanged from verified commit `6a3204b`.
The shared-nonce direct two-world coupling preserves the actual
pre-/post-challenge budget split. Its numerical leading coefficient is
`2.00000000000001034`, below the target coefficient 4 at 122 salt bits.
`SharedPinnedAdaptive`, `SharedPinnedConditional`, `SharedPinnedRestricted`
and `SharedPinnedFinal` lift and compose the coupling. Lean rounds the charge
to `3*(t+1)/2^122`; `NonceChainLayout.chain_budget` absorbs nonce-generator
error into the 120-bit target. Commit clears six high salt bits.

The earlier verified milestones include `b3add57` (66,784 bytes),
`dc4dd60` (66,768 bytes), `6a3204b` (66,752 bytes), and `95e2306`
(66,736 bytes), starting from parithosh's submission
`5b22c857-2c19-4975-8b87-e730b92c1efa`
(commit `c1e4e5347a401931539e5df5a234c6367365124d`).
Inherited notes and credits follow unchanged.

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
