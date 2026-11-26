# 65,544-byte RV64 candidate

The manifest digest is `fec9db3e3ef28dddc1ed54cede480853a913590e4cef8b527d491ce1adf7f4eb`.
The declared Pareto bounds are **720,710,940 commitment cycles**, **260,000 opening cycles**, and
**65,544 proof bytes** at 128 requested positions. The commitment and checker use the position-tagged two-call leaf from the pinned baseline.

## Universal opening bounds

Lean proves the official prover-cycle field for every 128-position batch. The commitment
uses at most **720,507,500 cycles** and **56,030,463 public calls**. The opening program
uses at most **207,588 cycles** even for an arbitrary trapdoor and arbitrary oracle replies.
Their combined bound of **720,715,088 cycles** fits the **720,970,940-cycle** claim.

Lean also proves the official **65,544-byte** bound. It bounds the proof list returned
by the actual ABI for every 128-position opening, arbitrary trapdoor and oracle replies.
The spread opening attains 65,544 bytes. Independent instruction analysis tightens
the opening cycle bound to 198,316.

The binary analysis starts at the ABI entry. It checks both possible paths of an unresolved
branch, validates frame and output writes, and follows the 128 record iterations. Each record
advances the cursor by 3,633 bits and marks the cap endpoint at heap index
`512 + position / 32768`. The scan of each adjacent pair sets its parent if either child is
present and emits the missing child exactly when one is present. Each low field advances
by 224 or 240 bits, and each group of up to four high digits advances by 31 bits.
The two paid levels round their group counts separately.
The heap flags start at zero under the opening ABI. Their addresses fall below the
trapdoor, serialized positions and image data, and the opener's copy of its data table
ends before the flag array.

Lean's `Frontier.cursor_bound` proves the bit limit of 524,352 for this flat scan, including
duplicate endpoints. If a level has `a` active children, `b` active parents and `f` missing
siblings, then `a + f = 2*b`. Applying this identity over the nine levels bounds the shared
frontier by 59,328 bits. Eight-byte rounding gives 65,544 bytes. A fault produces an empty
proof and can only shorten the charged prefix.

The binary analysis bounds startup and all records by 148,097 cycles, cap initialization by
19 cycles, the nine levels together by 50,177 cycles, and the return by 23 cycles.
The instruction-to-loop correspondence is checked by an external bit-vector analyzer using
Z3. From the final cursor and saved frame, `Return.batch_return` proves
that the delivered instructions halt successfully in 23 cycles. The theorem
`CommitGolf.Challenge.batch_return_proof` carries the bound through the contest's proof
loader. `HonestProofSize.scored` and `HonestProverScore.profile` separately prove the official
size and cycle bounds in Lean from the submitted machine images.

## Position-tagged leaf

The first permutation takes the first 200 bytes of the 256-byte entry. The second takes
an eight-byte position tag, 16 bytes containing the zero-extended 120-bit salt, the
last 88 bytes of the first response, and the last 88 entry bytes. Thus 32 entry bytes
occur in both permutation inputs. The tag is `4152 + 256 * index`. The low 240 output
bits of the second call form the leaf digest. These are the inputs of the baseline
`pinnedFirstInput` and `pinnedSecondInput` definitions.

`checker_layout.py` follows the compiled checker from singleton entry to its first
parent query for both parities with 23 arbitrary upper position bits. It checks every
input word against these definitions and the four digest words as received by the parent.
The binding proof uses the recorded public queries for both leaf permutations and every
parent needed to authenticate an opened position. Repeated positions in the same depth-nine
subtree must agree on its root.

## Executable

The commitment samples a 192-bit key. Each 4,096-leaf tile uses 342 forward permutation queries
for salts. A query has a zero prefix, a marker, a block address, and the three key words.
Moving the marker within the 25-word window distinguishes up to sixteen queries per counter
store. Twelve nonoverlapping 120-bit lanes leave 160 unused output bits. Lane zero uses the
last two words. The commitment first hashes lane zero's entry prefix, then places the last two
generator words into that lane's second-call salt slots. For every lane it writes the
first reply 32 bytes before the entry start. This leaves the overlapping entry words
intact for the second call. In each binary tree query the right child's top halfword identifies its depth.
The leaf tag is 65535, and internal child tags are their depths from 1 through 23. Each paid continuation hashes a full intermediate
reply followed by 32 zero bytes. The right operands distinguish these two query forms. Each
level has a guard slot so the last paid node also has zero space to its right. The selected
moduli project the high word at mixed-radix levels.

The opener reconstructs each salt from the trapdoor key and index. It emits 128 records of
3,633 bits, then the shared cap frontier. The ten lower digits occupy one 102-bit integer.
At the two paid cap depths, up to four base-211 digits occupy each 31-bit integer. The two
levels flush their final groups separately. The checker reconstructs every requested path,
checks agreement for repeated cap groups, and checks the root, the proof length and trailing
alignment bits.

## Checks

| Check | Result |
| --- | --- |
| Contest source and manifest preflight | Passed for the digest above |
| Reproducibility | Zig 0.14.1 with its bundled linker reproduced the delivered manifest byte for byte |
| Independent commitment control-flow audit | 325,149,296 steps, 56,030,463 public calls, 720,507,500 cycles on the successful path |
| Full RV64 run, 128 positions spread evenly across the tree | 65,544 proof bytes, 173,631 opening cycles, 128 opener calls, 12,031 checker calls, accepted |
| Full RV64 run, 128 contiguous positions | 58,408 proof bytes, 154,333 opening cycles, accepted |
| Additional runs | Accepted scattered, tile-boundary, final-index, empty, 129-position and 512-position openings. Negative tests rejected changed values, roots, proof bits, truncation and extra bytes. |

The machine runs use a fixed test permutation, compression function and seed. The instruction
audit reads the delivered commitment code, treats all memory loads as unknown, and checks the
loop latches, syscall modes and fixed costs. The full commitment run also tracks whether loaded
data influences control flow, addresses or syscall arguments. These are development checks.
The universal bounds above also cover choices of positions and oracle replies outside this test suite.

## Lean proof status

`Solution.lean` defines the entrant from `CommitGolf.Artifact.submission`. Its
`submission_matches_artifact` and `image_admission` theorems concern the delivered images.
`ReconstructedProfile`, `ReconstructedRadix`, `ReconstructedCap` and `ReconstructedRoutes`
cover the schedule, bounded digit round trips and the tight aligned size bound in the format
model. `ReconstructedGenerator` proves the modeled query encoding identifies its tile, group
and key. It proves the opener recovers the commitment counter at every position and that
each position and salt bit has a distinct query-and-output-coordinate pair for a fixed key.
`ReconstructedEmpty` proves five-cycle, zero-query successful execution through the
submission ABI for the empty opener and the checker with an empty proof.
`ReconstructedSeed` proves that the actual commitment executes its first seven instructions,
samples 192 private bits into address 5,637,148,560, and charges ten cycles and zero public calls
before the remaining instructions execute.
`ReconstructedQueries` proves at most 100 calls per requested position in the honest
checker traversal model, including shared cap nodes and partially occupied subtrees.
The spread batch costs exactly 12,031 queries in that model.

`ReconstructedCommitScored` proves commitment termination and the commitment cycle bound
for the delivered image. `ReconstructedLeafCodeReceipts` checks every decoded slot in the
4,096-entry tile. `ReconstructedLeafComplete` follows the actual code through every one
of the 16,777,216 positions. It proves that after 217,075,711 leaf-phase instructions,
the heap contains every expected position-tagged digest and the parent workspace is fresh.
`ReconstructedLeafTape` identifies the salt seen by every leaf with the corresponding
120-bit coordinate of the keyed permutation in the hiding experiment.
`ReconstructedCommitMachine` proves the emitted commitment reaches HALT with the correct
root, serialized tree and generator window for every possible key. `ReconstructedCommitOutcome`
gives probability-one success and averages the result over the exact key distribution.
`ReconstructedEncoding` proves the full reference serializer meets the batch byte bound.
For every fixed key and message, the opening image emits the requested salts, sibling
digests and shared frontier in the stated order. The resulting commitment and proof have
the distribution used by the hiding game for every opening cardinality and query budget.

`CheckRecords.positive` follows the checker through the local records, including malformed
headers and conflicting subtree roots. `CheckCapInitial.nine` follows the shared frontier
through all nine levels. An honest record costs 84 public queries, and the upper tree costs
at most 16 times the number of opened positions. `CheckTail.run` verifies the final length,
four root words, trailing padding and halt status. The verifier loads the manifest named above
and checks equality with the submission used by every certificate field.

## Baseline provenance

The remainder of this file is the historical README of the inherited 66,736-byte submission.
This reconstruction directly reuses its proof libraries for public-query recording,
position-tagged leaves and hiding. [Baseline source at commit 718260f](https://github.com/Layr-Labs/commit.golf/tree/718260f234a0fd6293b255041fe7748090f52c22/submission-pareto).

# 241-bit leaves and three-bit record heads

## Width-241 binding

The adaptive shared-query binding proof at width 241 uses the same 238-bit
compression-dominated hazard envelope. Its numerical maximum, including the
private replay allowance, is `0.902512468156617 * q/2^120`, around
`q/2^120 = 0.7926005326`: about 9.75% margin. The forward and inverse
permutation pair fibers have size at most `2^1360`; inverse unary fibers
remain bounded by `2^896`. `JointOracle241*` and `Leaf241ReplayProbability`
connect the common envelope to the recorded executable replay. The earlier
width-242 modules remain intact.

This candidate starts from the verified 66,752-byte commit
`6a3204b55fbb2b3378e3631c1c9db6672a0537c4`. The 121-bit-salt alternative
was researched only: the current linear hiding envelope has coefficient
`2.00000000000000517` against target 2 after generator error, so it does not
fit without a stronger argument. Either isolated one-bit cut saves exactly
16 bytes at 128 records.

## Split-budget hiding at 122 bits

The shared-nonce two-world candidate has leading charge
`2*(a+b)/2^122`, where `a+b=t` is the actual pre-/post-challenge query split.
Including the existing conservative nonce-generator error and high-tail
errors gives a uniform numerical envelope of approximately
`2.00000000000001034 * (t+1)/2^122`, below the target coefficient 4.
`SharedNonceHits.lean` proves joint input and cached-output guess bounds for
any collection of message worlds sharing one nonce tape.
`SharedOracleCoupling.lean` proves a direct two-world distance bound charged
once on a common reference execution. `HidingPrefixBudget.lean` retains the
query count of the actual lazy prefix and its complementary observer budget.
`SharedPinnedRows.lean` couples both row samples with correct marginals and
proves a joint row-hit bound `2/2^122 + 2*card(I)/2^1343`.
`SharedPinnedAdaptive`, `SharedPinnedConditional`, `SharedPinnedRestricted`, and
`SharedPinnedFinal` lift and compose this coupling into the reference hiding
certificate. Lean rounds the charge to `3*(t+1)/2^122`; `NonceChainLayout.chain_budget`
absorbs the nonce-generator error into the 120-bit target.
The commit machine clears six high salt bits with its certified 58-bit high-word mask.

## Delivered 122-bit salt artifact

This work builds on the locally verified 66,784-byte milestone
`b3add57c09865e7ba4bbb556f11f7c1decd5a20c` and its 66,800-byte predecessor
`ae0f257`, starting from parithosh's submission
`5b22c857-2c19-4975-8b87-e730b92c1efa` (commit
`c1e4e5347a401931539e5df5a234c6367365124d`).
Its credits and ancestry are retained below.

The claim is **66,736 proof bytes**, **756,825,559 commitment cycles** and
**4,065,093 opening cycles**. Internal digests remain 238 bits, leaves are
241 bits, salts carry 122 bits, and binding and hiding target 120 bits.
Commit keeps the low 49 bits of each leaf's top doubleword. The checker
uses matching 15-bit shifts to truncate its computed leaf.

`HeadStreamThree.lean` keeps 45 complete head bytes and 29-byte digest bodies
in each main record. The remaining three live salt/leaf head bits follow the
digest-remainder stream, eight heads per three bytes. The final partial group
is zero-padded. At the scored maximum each record and its remainder bits
occupy 3,933 bits, and there are 128 cap digests of 238 bits each:
`128 * (3933 + 238) / 8 = 66,736` bytes.

The intermediate combined head uses two salt bits followed by one leaf bit.
The opener conversion pass has execution, byte-frame and exact cycle proofs.
Twelve padding instructions retain the existing instruction offsets and cycle bound.
The opening certificate establishes the exact serialized transcript and
the scored cycle and size bounds. Full-position-set opening fuel is `2^39`.
The three-bit codec proves inverse conversion and honest round trips, including
empty and missing-record cases. The checker has a 75-instruction restoration
pass followed by the existing unpacker and checker. Oversized virtual lengths
and incomplete records are rejected before proof-memory accesses.
Origin-parameterized memory preserves unaligned-word semantics; register
preservation uses abstract loader outputs. Checker fuel remains `2^40`.

The `JointOracle*` modules track the compression cache and forward/inverse
permutation trace together. Each adaptive public query consumes only its own
oracle's conditional hazard; private coins do not consume public budget.
`PinCallFibers.lean` and `PinCallNatCounts.lean` supply generic forward/inverse
pair and unary fiber bounds without expanding the encoding or passing through
real-valued cardinalities. `Leaf242JointMargin.lean` proves the joint survival
envelope fits `q/2^120`, including replay overhead, with probability capping at
large budgets. The leading normalized numerical envelope peaks near
0.902512468157, leaving about 9.75% margin. `Leaf242ReplayProbability.lean`
connects full sampled compression/permutation execution to the joint lazy model
and the actual recorded replay rows, including inverse queries.

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
