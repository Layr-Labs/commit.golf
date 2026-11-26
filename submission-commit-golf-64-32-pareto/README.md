# 14c08500 on the 64-32 track: 2,425,569,135 cycles at 65,472 bytes

This entry is our accepted Pareto entry `14c08500` (ekrembal's `1a30c52f` with a specialized parent loop in its commitment), re-certified for `commit-golf-64-32-pareto`, where a forward or inverse permutation call costs 30 cycles instead of 8. The three programs, the proof format and every proof byte are unchanged. Only the claim and the Lean proofs whose statements carried the 8-cycle price change.

| | `14c08500` on `pareto` | This entry |
| --- | ---: | ---: |
| Commit cycles | 1,653,371,596 | 2,425,124,556 |
| Opening cycles | 444,579 | 444,579 |
| Prover cycles | 1,653,816,175 | 2,425,569,135 |
| Proof bytes | 65,472 | 65,472 |

`claim.json` is `{"commitCycles": 2425124556, "openingCycles": 444579, "proofBytes": 65472}`. The commitment makes 35,079,680 permutation calls (two per leaf and 1,525,248 in the nonce chain) and 67,302,655 compression calls, so its bound grows by exactly 22 x 35,079,680 = 771,752,960. The opening makes no permutation calls and its bound is unchanged.

## What changed in the proofs

Every permutation call reaches the proofs through `execute_permutation_call` (`TwoPermutationSyscall`) and `Chain.chain_perm_call` (`NonceChainSyscall`); both now charge 30. Each block that contains a permutation call grows by 22 per call, fixed where the constant is first stated: a leaf costs 69 cycles instead of 25, a nonce-chain call 32 instead of 10, the leaf phase 1,157,832,703 cycles instead of 419,635,199; the compression-only parent phase keeps its 1,166,031,243. `Execution.lean` carries the organizers' 30-cycle form of the generic cost lemma (`oracleCycles_le_thirty`). In the checker, `ChainedCheckerRecordFinish` stated cycles = instructions + 7 x calls, which holds only at 8 cycles per call; it is now + 44 per processed record (two 30-cycle calls each), and the checker's per-record bounds grow by 44. Checker cycles are not scored. Instruction counts are unchanged everywhere. All modules in `Solution`'s import closure were rebuilt from scratch at the new price; modules outside that closure are inherited unchanged and may still carry 8-cycle figures.

Changed: `Execution`, `TwoPermutationSyscall`, `NonceChainSyscall`, `NonceChainLoop`, `NonceChainExec`, `NonceChainSetup`, `TwoPermutationPackedLeafRun`, `TwoPermutationPackedLeafGroups`, `TwoPermutationPackedLeafLatch`, `TwoPermutationPackedLeafInterface`, `TwoPermutationLeafRun`, `TwoPermutationLeafGroup`, `TwoPermutationAllLeaves`, `TwoPermutationCommitRun`, `TwoPermutationCheckerLeafRun`, `ChainedCommitPrefix`, `ChainedParentRun`, `ChainedCommitExecution`, `ChainedSerialization`, `ChainedCountedCommit`, `ChainedDeliveredCommit`, `ChainedDeliveredHiding`, `ChainedCheckerLeafRun`, `ChainedCheckerLeafReturn`, `ChainedCheckerLower`, `ChainedCheckerRecordFinish`, `ChainedCheckerRecordObserver`, `Solution.lean`.

## Credits

The construction and its certificate are ekrembal's `1a30c52f` with our commitment loop from `14c08500`; that entry's README follows unchanged below, and its figures are the 8-cycle ones.

---

# A specialized parent loop in 1a30c52f's commitment: 1,653,816,175 cycles at 65,472 bytes

This entry is ekrembal's accepted Pareto entry `1a30c52f` with a faster commitment program. The opening and check images, the proof format and every proof byte are unchanged, and so are the commitment value, the whole trapdoor and the sequence of oracle inputs. Only the commitment program and the Lean proofs of its execution, contents and cost change.

| Entry | Commit cycles | Opening cycles | Prover cycles | Proof bytes |
| --- | ---: | ---: | ---: | ---: |
| `1a30c52f` by ekrembal (base) | 2,353,177,256 | 444,579 | 2,353,621,835 | 65,472 |
| This entry | 1,653,371,596 | 444,579 | 1,653,816,175 | 65,472 |

`claim.json` is `{"commitCycles": 1653371596, "openingCycles": 444579, "proofBytes": 65472}`.

## What changed

The base hashes each internal node with one compression call or a chain of them, all through one generic parent loop: 1,814,456,675 of its 2,353,177,256 commit cycles. At heights 0 to 7 (16,711,680 nodes of four calls each; heights count from 0 as in the Lean modules, while the base's README counts these levels 1 to 8) a node costs 108 cycles there: a subroutine call, a 31-instruction packing routine, six instructions per continuation, an eight-instruction copy to the heap, and the loop.

- Heights 0 to 7 now run new code at commit words 45683–51100, which the base never executes. Each node is unrolled: its four calls, the packing of its two children in place, and a deferred mask (a child's truncation is finished when its parent reads it): 69 cycles per node at heights 0 to 6 and 72 at height 7, which also finishes its own mask, plus 3 cycles per group of 16 nodes. The code then jumps to the base's own level header for height 8 (word 45298), and the base's code computes heights 8 to 23 and the root.
- The base's separate leaf-mask pass is folded into height 0: word 45128 now jumps to the new code, which finishes each leaf's mask when it reads it.
- The image keeps the base's parent block at words 45129–45682 and stays at 933,932 bytes.

The oracle sees the same inputs in the same order as with the base, so the commitment and the trapdoor are the base's, and the base's opener and checker run unchanged.

## Lean changes

New modules: `ChainedFastFrontier`, `ChainedFastLayout`, `ChainedFastCode`, `ChainedFastOps`, `ChainedFastValues`, `ChainedFastPack`, `ChainedFastView`, `ChainedFastNode`, `ChainedFastFrame`, `ChainedFastControl`, `ChainedFastLoop`, `ChainedFastPhase`, `ChainedFastContent`, `ChainedFastEntry`. Changed base modules: `ChainedParentRun`, `ChainedParentContentRun`, `ChainedLeafContent`, `ChainedHeapOutput`, `ChainedNonceFrame`, `ChainedCountedCommit`, `ChainedCommitContent`, `ChainedCommitPrefix`, `ChainedParentInit`, `TwoPermutationPackedZeroLeaves` (two theorems about the old jump at word 45128 removed), the cycle constants in `ChainedCommitExecution`, `ChainedDeliveredCommit`, `ChainedSerialization` and `ChainedDeliveredHiding`, and `Solution.lean`. The opening, checker, binding and hiding proofs are the base's.

## Credits

- Base: `1a30c52f-9182-4665-9235-5b577768c559` by ekrembal: the chained internal hashing, its schedule, and the generic parent loop whose code and proofs the new loop follows.
- The leaf-mask module edited here was introduced in parithosh's `5b22c857-2c19-4975-8b87-e730b92c1efa` with a 245-bit mask. ekrembal's entries narrowed the mask in steps to 238 bits in `89c80b71-533c-4e7f-9a65-b533bd13aec3` and carried that version unchanged to `1a30c52f`; the new height-0 code applies that 238-bit mask.
- Everything else, and the credits it lists, comes with the base. The base's README follows unchanged; its figures describe the base, not this entry.

---

# 65,472-byte opening proofs via chained internal hashing

This entry certifies **65,472 proof bytes**, **2,353,177,256 commitment cycles** and
**444,579 opening cycles**, a 1,200-byte cut from our 66,672-byte entry `ab6788d5`.
Internal Merkle nodes at heights 1-16 use domain-separated chains of 4-8 compression
calls with 256-bit states, and only the final output is truncated: heights 1-8 use 4
calls and 234 bits, height 9 uses 6 calls and 233 bits, heights 10-15 use 8 calls and
232 bits, height 16 uses 4 calls and 234 bits, and heights 17-24 use 1 call and 238 bits.
Leaves (238 bits, two permutation calls) and 121-bit salts are unchanged.
`Solution.lean` imports the chained certificate (`ChainedDeliveredHiding`), which is derived
from the delivered commit, opener and checker images. The section "Chained-internal
research branch" below gives the full details. Older sections are historical.

# 121-bit salts and seven-bit tail streams

This local candidate branches from verified `e4cf27a` (66,688 bytes).
It targets **66,672 proof bytes**, **756,825,559 commitment cycles** and
**5,004,960 opening cycles**. The current machine certificate and official
verification status are reported separately; these figures alone are not a
verification result.

## Exact physical layout

The salt mask retains 121 bits; the top word is masked to `2^57-1` using
a seven-bit shift. Leaves and internal digests retain 238 bits.
Each opening record uses 44 body bytes, plus a seven-bit tail stream packing
eight tails into seven bytes. Internal digests use 29 body bytes and a
six-bit remainder stream. The worst case is exactly:

```text
44*128 + 112 + 29*2048 + 1536 = 66672 bytes
```

`HeadStreamSeven` proves conversion/restoration, honest round trips, the exact
maximum, empty-input and missing-record behavior. The opener retains its
zero-format prefix and runs a native seven-bit postpass. The checker restores
the seven-bit stream, then composes the zero-format restoration and existing
unpacker. Both restoration stages have capacity/incomplete-record guards and
origin-preserving memory proofs. The observation theorem covers malformed
inputs as well as honest acceptance. Opening fuel remains `2^39`; checker
fuel remains `2^40`. The manifest delivers the exact certified instruction
images, not an abstract codec in place of machine execution.

## 121-bit hiding reserve

`SharedPinnedCacheCap`, `SharedPinnedPairCoupling`,
`SharedPinnedCappedConditional`, `SharedPinnedCappedRestricted` and
`SharedPinnedCappedFinal` charge the cached-address exception once across
both worlds and the complete adaptive observer trace. The leading charge is
`min(2*t, t + 3*LENGTH)/2^121`, rather than `2*t/2^121` at every budget.
`Salt121CappedMargin` absorbs the unchanged nonce-generator and high-tail
errors with an explicit relative reserve of `1/100000000`.
`NonceChainSecurity.chain_reference_hiding` uses the composed bound.

## Preserved binding margin

The minimum leaf width under the adaptive joint-survival reduction with at
least 2% numerical margin remains **238**. The normalized numerical maximum
is `0.9025124681566164`; width 237 fails at `1.276345372677903`.
`JointOracle238*` charges adaptive compression and forward/inverse
permutation queries to their own oracle. `Leaf238JointMargin` proves a
2% reserve including replay overhead; `Leaf238ReplayProbability` connects
it to recorded executable replay. Commit keeps 46 bits of the leaf's top
doubleword and the checker uses matching 18-bit shifts.

Earlier verified milestones include `b3add57` (66,784 bytes), `dc4dd60`
(66,768), `6a3204b` (66,752), `95e2306` (66,736), and `e4cf27a`
(66,688). Inherited credits and historical notes follow.

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

## Chained-internal research branch

The planned 65,472-byte layout keeps 121-bit salts and 238-bit leaves. Internal
heights 1–8 use four calls and 234 final bits; height 9 uses six and 233;
heights 10–15 use eight and 232; height 16 uses four and 234; heights 17–24
retain one call and 238 bits. All intermediate outputs remain 256 bits.

`ChainedQueryGraph` proves disjoint work for distinct completed chains on good
transcripts. `ChainedEncoding` supplies an explicit injective height/stage
encoding. `ChainedGraphHazard` bounds collision and backward-link targets by
twice the number of prior fresh queries. `ChainedGraphAdaptive` accumulates
these hazards for adaptive programs. `ChainedGraphSampler` instantiates that
bound for a chronological lazy compression sampler with both directions of any
fixed permutation. `ChainedSchedule` checks the proposed resource arithmetic;
its checker bounds are not yet native execution bounds.

`ChainedWeightedExponent` proves a generic finite product-survival envelope
from a weighted count bound and the density inequalities. This is arithmetic
about a survival potential, not yet a probability theorem for the adaptive run.

`ChainedCompletion`, `ChainedCompletionCounter`, and `ChainedCompletionWork`
prove reply-independent completion prediction, the exact per-height counter
update on good extensions, and the weighted work bound for the predicted update
before sampling its reply. A safe dummy reply supplies this work bound even when
the eventual actual reply causes a graph exception.

`ChainedFinalHazard` bounds fresh final collisions intersected with good graph
extensions; it never conditions the reply distribution on graph goodness.
`ChainedLeafHazard` charges forward and inverse permutation hazards to the
permutation-query count alone. `PredictableSurvival` and
`WeightedAdaptiveSurvival` prove the backwards survival-potential induction for
models supplying these local hazards and predictable counter updates.

`ChainedGraphCache` connects chronological graph rows to a lazy cache, and
`ChainedCounterVector` combines internal and permutation counter arithmetic.
`ChainedJointOracle` retains both the graph and a lazy permutation trace; its
cache-state projection and private/forward/inverse handler projections are
proved. The compression-handler projection is not yet proved.

`ChainedJointObserver` supersedes that reimplemented sampler: it runs
`JointOracle238.handler` directly and records fresh compression answers in an
observer graph. Answer/base-state projection for arbitrary adaptive programs,
cache/graph agreement, and observer validity preservation are proved.
`ChainedStoppedState` proves stopped-counter validity preservation and the
pre-reply weighted-work forecast. `ChainedSourceUniform` transports uniform
events between sampling instances without identifying their syntax.
`ChainedStoppedHazard` composes final-output and forward/inverse leaf hazards.
`ChainedStoppedModel` instantiates `PredictableSurvival.Model`, and
`ChainedStoppedInitial` proves the empty-state survival bound with one dummy
leaf factor of value one. The finite exponential uses work ceiling `limit+1`.
`ChainedObserverGraph` proves the graph-exception bound for the actual source
engine. `ChainedStoppedProjection` transports it to the stopped process and adds
it to the survival failure probability, without conditioning on graph goodness.
`ChainedStoppedTerminal` proves support-wise terminal validity and covers raw
leaf/final collisions by that joint failure event.
`ChainedReserve` and `ChainedSecurityBound` specialize to the approved schedule
and `Q=q+2^32`, retaining the `Q+1` work shift and graph error. For every `q≥1`,
the terminal raw leaf/final failure probability is at most `15*q/2^124`, a
pointwise `1/16` reserve below the binding target `q/2^120`.
The common `BindingReplayEvidence` and binding-reduction theorems now accept a
replay-overhead parameter; `ChainedReplayBudget` specializes it to `2^32`.
The unchanged certificate retains the default `2^31` and its legacy margins.
`ChainedRecordedWitness` embeds recorded full-width chains into the observer
graph and covers pinned-leaf witnesses. `ChainedRecordedProbability` transports
their reserve to the sampled-oracle game and proves binding from replay
evidence. `ChainedOpeningPaths` compares variable-width recorded paths;
`ChainedCheckerReplay` derives that evidence from accepted machine traces,
conditional on `AcceptedTraceRefines` for the new checker.
`ChainedContinuationCode` decodes a standalone 19-word native continuation
fragment. `ChainedContinuationHeader` proves its eight-instruction domain
preparation and register frame; `ChainedContinuationMask` proves final masking,
the zero-continuation path, and invalid-mask-access rejection.
`ChainedContinuationFrame` composes abstract word-store frames and proves that
header preparation preserves all four chaining-value words.
`ChainedContinuationTail` proves back-edge execution, counter decrement, and
preservation outside the stage-domain word, including all four chaining words.
`ChainedContinuationIteration` proves each compression-plus-tail iteration costs
six instructions, thirteen cycles and one public call. `ChainedContinuationLoop`
proves repeated execution and public-query bounds under concrete compression
arguments. `ChainedContinuationRun` proves terminal control/counter invariants
and composition with the single final mask. Delivered-image integration remains outstanding;
this fragment is not a certified chained commitment.
`ChainedContinuationDomain` proves the four stored header words, including the
`7*h` initial stage tag, two zero words and the high domain bit.
`ChainedContinuationInput` identifies the actual 64-byte read with the canonical
next-stage encoding. `ChainedContinuationContent` proves header preservation
across full-width reply writes, stage-tag advancement, exact 256-bit reply
readback after the tail, and refinement of the repeated native loop to the
canonical continuation oracle program. Final truncation remains outside that
loop.
`ChainedFirstPackCode` decodes a 31-instruction first-stage child packer;
`ChainedFirstPackExecution` proves execution in 31 cycles with zero public calls
under checked image, PC and memory-access premises. All eight source words are
loaded before any destination word is stored. `ChainedFirstPackValue` proves
the contiguous 238+238-bit layout and exact canonical first-stage encoding.
`ChainedFirstPackContent` proves the actual stored words and memory/register
frames using a PC-free data projection. `ChainedFirstPackInput` identifies
the actual 64-byte read with the canonical height/child input.

`ChainedContinuationEntry` composes the entry branch, header, full-width loop,
and final mask with exact instruction/cycle/public-call charges.
`ChainedCommitCode` defines and decodes the complete 550-word parent phase:
24 descending heap levels share the first-stage packer and continuation, retain
full-width intermediates, apply the selected final masks, then copy the root
and halt. `ChainedCommitGeometry` proves its call/back edges, register setup,
and schedule arithmetic. The arithmetic is not a whole-machine execution bound.

`programs.json` now delivers this parent phase at word 45133, with commitment
fuel raised to `2^31`. Other code bytes, embedded data, and the memory ABI are
unchanged. `ChainedCommitFetch` checks the exact artifact words and instantiates
the packer and continuation execution theorems at their delivered addresses.

`ChainedHashState`, `ChainedContinuationReturn`, and `ChainedHashExecution`
compose the actual shared hash call: `JAL` into the first-stage packer, its
`JALR` return, the first compression syscall, copying the outer link register,
and the continuation's final return. For `m <= 7` remaining calls, execution
takes `35 + continuationInstructions m` steps,
`42 + continuationCycles m` cycles, and `m + 1` public calls, under the stated
entry/access premises. Support-wise return-PC and caller-register frames and
a structural public-query bound are proved, including the zero-continuation
case. `ChainedHashInput` identifies the actual first syscall with the canonical
height/child encoding. These are call-level results, not a level/heap induction.

The image definition and leaf-phase contract now live in
`TwoPermutationPackedCommitImage` and `TwoPermutationPackedLeafInterface`.
The delivered leaf fetch/latch chain no longer imports the legacy parent-image
proof. `ChainedCommitPrefix` composes the actual leaf execution and zero-mask
pass, starting from `Chain.BodyRegs` and reaching parent PC 184628 in
236,134,409 steps, 471,015,433 cycles, and 33,554,432 public calls. This prefix
does not include nonce generation or any internal-parent execution.

`ChainedLevelCall` checks each height's setup instructions against the delivered
image and composes them with the shared hash. It proves the outer call reaches
PC 186612, preserves the scratch ABI, uses `calls h` public queries, and returns
to the height's heap-copy suffix. Cursor-loop induction and the 24-level
content invariant are still outstanding.

`ChainedMaskValue` proves word-level truncation for every scheduled width and
that the actual four-instruction final mask realizes it.
`ChainedContinuationMeaning`, `ChainedHashMeaning`, and `ChainedLevelMeaning`
compose the canonical first query, all full-width continuation replies, and
this single final truncation into the delivered per-height hash trace. The
proof covers both zero and positive continuation counts; it stops before
copying the digest into the serialized heap.

`ChainedScratchFrame` and `ChainedHashMemory` prove support-wise preservation
of aligned, bounded heap words outside the 64-byte scratch buffer.
`ChainedHeapCopy` and `ChainedHeapCopyContent` prove the delivered eight-instruction
copy, exact digest readback, and unrelated-word frames under source/destination
separation. `ChainedLevelBody` separates the one-time five-instruction header
from the repeated three-instruction call prefix. `ChainedNodeStore` composes
the actual repeated call and copy in `46 + continuationInstructions (calls h-1)`
steps, `53 + continuationCycles (calls h-1)` cycles, and `calls h` queries,
under explicit entry/access premises. Its content theorem stores the canonical
chained, finally truncated digest under child-content and separation premises.
These results stop before the cursor decrements and conditional back edge;
the node-count and full-heap induction are not proved.

`ChainedCursor` proves the separate two-instruction decrement fragment and its
source/target, register, memory and PC facts. `ChainedBranch` proves the actual
abstract-state BNE execution and delivered per-height jump targets.
`ChainedNodeStep` composes the full delivered node execution in
`parentNodeSteps h` steps and `parentNodeCycles h` cycles, with `calls h` public
calls and the conditional back/exit PC. No three-instruction whole-state prefix
equality is used. `ChainedNodeFrame` proves the post-BNE register/memory frames
using projections of the branch-case state equalities, and composes them into
the complete node's cursor, preserved-register, scratch-ABI and memory frames.
`ChainedLevelState` and `ChainedLevelLoop` prove node-count induction, including
the zero-count case, the last-node test, actual execution and query charges.
`ChainedLevelFrame` proves full-level cursor displacements and memory
preservation outside its destination span. `ChainedNodeMeaning` extends the
canonical digest readback through both decrements and BNE.
`ChainedHeapAddress` and `ChainedHeapLevel` instantiate the level's access
premises from the delivered heap geometry. `ChainedLevelShift` and
`ChainedHeapTransition` prove the actual ending shift and the next-height
entry invariants across all 23 adjacent pairs of the 24 levels.
`ChainedParentInit` bridges the leaf/masking prefix into the first heap level.
`ChainedParentLevels`, `ChainedParentPost`, `ChainedRootExecution` and
`ChainedParentRun` compose all 24 levels, their terminal register/PC facts,
root copy and successful halt. `ChainedCommitExecution` composes the seed and
nonce expansion too: the complete native commitment takes 1,636,500,908
instruction steps, 2,353,177,256 cycles and 102,382,335 public calls under its
explicit entry contract. The step/query counts meet the delivered fuel and
commitment-query limits. `ChainedDeliveredCommit` instantiates the execution
theorem for the exact generated artifact and proves success and exact cycles
and public calls for every supported commitment result.

`ChainedHeapWords`, `ChainedHeapMeaning`, `ChainedLevelContent` and
`ChainedParentsContent` prove canonical child serialization, fixed-oracle node
meaning, preservation of completed nodes and the semantic induction across all
24 levels. `ChainedHeapModel` constructs the variable-width reference tree and
proves agreement with every completed heap node from an explicit initial-leaf
content invariant. `ChainedRootWords` and `ChainedRootContent` prove root-copy
readback using projected word stores and frames. `ChainedParentContentRun`
composes that readback with all 24 interpreted parent levels without expanding
their computation. `ChainedLeafContent` initializes the reference heap from the
actual delivered leaf/masking prefix, independently of the legacy packed-parent
meaning contract. `ChainedCommitContent` composes leaf initialization, all parent
levels and copied-root meaning. `ChainedNonceFrame` preserves nonce storage
through all parent levels and the root copy, and through the complete commitment
body. `ChainedSeedContent` instantiates the body's register and salt-content
contracts with the actual artifact entry, message and private seed.
`ChainedCountedCommit` proves the fixed-oracle artifact run is exactly the
seed-sampled body execution with 102,382,335 public calls. `ChainedHeapOutput`
preserves all cached heap nodes through the root copy and complete body.

These are supporting research modules, not a certificate for the new layout.
`ChainedSerialization` uses abstract-state readback and execution-projection
lemmas, following the certified serialization chain, to extract the root,
every cached node, and every salt from the actual artifact's `readCommit`.
`ChainedCodecGeometry` proves a 30,208-bit cap-frontier bound with 234-bit
height-sixteen digests and 238-bit digests above them. Together with the
3,856-bit lower records, this gives layout arithmetic of at most 65,472 bytes
for any set of at most 128 positions, including an empty layout for no positions.
This is not yet a size theorem for an implemented machine codec.
`ChainedSplitCodec` gives generic split-width payloads and structural round-trip
proofs over arbitrary low/high width specifications. Abstract bit reads avoid
per-height dependent-index rewrites. `ChainedOpeningCodec` instantiates the
482-byte records and variable-width footer, proves complete packet round trips
and the 65,472-byte encoded-size bound, and extracts canonical payloads and
the exact record count from successful parsing. Length and padding checks
reject malformed encodings; empty packets are supported. These are pure codecs,
not yet refinements of the delivered native opener/checker.
`ChainedTailAppend` and `ChainedTailFlush` provide decoded standalone native
fragments for accumulating a variable-width tail and writing one complete byte.
They prove register/memory effects and actual execution charges of three and
four cycles respectively, with zero public calls; flushing requires a valid
destination address. Record/footer tail widths fit the accumulator's six-bit
field bound. These fragments have not been installed into the delivered images
or composed into complete packing/parsing loops.
`ChainedTailEmit` composes append, an actual native guard and byte flushing;
it takes four cycles without flushing and eight with flushing, with zero
public calls. `ChainedTailEmitFrame` proves its byte/register frames.
`ChainedTailFinish` writes a final partial byte only for a nonempty remainder,
in one or three cycles, and preserves zero padding under the accumulator bound.
These blocks have exact standalone instruction images and arbitrary-image
fetch interfaces; their delivered-image integration remains open.
`ChainedTailReadCode`, `ChainedTailRefill`, `ChainedTailExtract` and
`ChainedTailRead` implement the inverse field operation: guarded byte refill,
low-field extraction and residual-buffer advancement in seven or twelve cycles,
with zero public calls and no memory writes. The whole-packet inverse parser
and its length/padding checks are not yet installed in the delivered checker.
`ChainedTailTraverseCode` gives the 17-word scratch-row traversal image;
`ChainedTailLoad` proves its value/width byte loads and source advance.
`ChainedTailTraverseStep` composes one row, guarded emission, decrement and
back edge in at most thirteen cycles with zero public calls. Whole-row-count
induction is proved in `ChainedTailTraverse`, using an irreducible final-state
function with explicit zero/successor equations. `ChainedTailTraverseEntry`
composes the entry guard, all rows and the final byte: at most `13*n+4` cycles,
zero public calls, and two cycles for empty input with an empty accumulator.
These operational bounds require explicit readiness/access premises; scratch-row
memory refinement is described below.
`ChainedTailBits` interprets native words as little-endian bit lists and proves
byte agreement with `SplitCodec.packBits`. `ChainedTailEmitBits` connects actual
accumulation, guarded byte writes, residual shifts and final zero padding to
that interpretation. These per-field refinements are composed into the
per-payload memory theorems below, but not yet a delivered-image packet controller.
`ChainedTailReadBits` proves the native inverse field's extracted bits,
residual buffer and residual count. `ChainedTailRowBits` connects scratch-row
loads and complete emission-row byte effects to the bit-list codec.
`ChainedTailValidate` computes a native flag for an exact supplied end pointer
and zero residual bits. `ChainedTailParseCode`, `ChainedTailParseStep`,
`ChainedTailParseTraverse` and `ChainedTailParseEntry` compose the 21-word
inverse-row image, stores and loop: at most `17*n+4` cycles, zero public calls,
and four cycles for empty input. Their execution theorems require explicit
readiness/access premises. This is not yet a whole-packet parser: construction
of record/footer scratch rows, packet-level memory refinement and installation
in the delivered opener/checker remain open.
`ChainedAlignedBits` and `ChainedPacketDescriptors` derive the actual low-byte
copies and two-byte tail rows from arbitrary codec payloads. The record has
479 low bytes, three packed tail bytes and 34 scratch descriptor bytes;
footer low bytes occupy 29 bytes per node. `ChainedDescriptorMemory` proves
the descriptor array's native loads and the equivalence between record/footer
segment memory views and the complete encoded packet. `ChainedTailBuffer`
proves the accumulator and output-cursor invariants for complete native rows.
These interfaces do not yet construct descriptors in a delivered machine.
`ChainedTailSourceFrame` preserves the immutable descriptor table under explicit
source/output separation. `ChainedTailPlan`, `ChainedTailPacking` and
`ChainedTailMemory` prove that all native rows and final padding write exactly
the generic packed tail, including empty input and zero-width fields.
`ChainedByteWriteView` proves bounded byte-array readback and untouched-byte
frames. `ChainedPayloadMemory` preserves the already-copied low body and yields
the exact complete record/footer encoding. `ChainedPayloadExecution` couples
this result to the actual traversal execution and its `13*n+4` bound, under
explicit image, entry, readiness and access premises. Native construction of
the low body/descriptors, whole-packet inverse refinement and packet controllers
are still missing; no opener/checker bytes are changed by these results.
`ChainedByteCopy`, `ChainedFieldDescriptor`, `ChainedLowCopy`, `ChainedFieldBuild`
and `ChainedFieldCode` provide exact native field-construction images. A field's
low body is copied and its value/width row initialized in `4*n+5` cycles, with
zero public calls. The memory proof permits forward in-place compaction under
an explicit no-unread-source-clobber premise and separates scratch rows from
the copied body. Image fetch, pointer/register frames and complete execution
are proved. Record/footer iteration refinement, deriving raw source views from the cached
opening, packet inverse refinement and delivered controllers remain open.
`ChainedFieldFrame`, `ChainedCopyGeometry`, `ChainedRawField` and
`ChainedFieldHeader` derive the copy/access premises from non-wrapping pointer
ranges and prove the complete field write plan, preservation of completed
output/descriptors and unread raw bytes, and trusted skip/width initialization.
Initialized fields execute in `4*n+7` cycles with zero public calls. The raw
view includes the high byte, optional source padding and remaining packet;
zero-sized low bodies and zero-width high fields are covered.
`ChainedFieldPrefix`, `ChainedFieldsMemory` and `ChainedFieldsExecution` compose
arbitrary raw fields, preserving existing output/descriptors and unread input.
They construct the complete low body and descriptor table from raw input, in
exactly `4*lowBytes+7*fields` cycles and zero public calls under explicit fetch
and memory-range premises. `ChainedPayloadFields` instantiates this construction
for typed codec payloads, rather than assuming initialized bodies/descriptors.
`ChainedRecordFields` proves the 498-byte raw record stride and 2,035-cycle
record construction cost; footer construction uses 30 raw bytes and 123 cycles
per node. These are field-list-plan costs, not whole-controller bounds; tail
packing and outer controller instructions are excluded.
The cached-opening raw-view bridge and whole-controller execution remain open.
`ChainedOpeningControllerCode` supplies a standalone 2,248-word forward
postpass with all native decoding and fetches proved. It constructs each
record's low body and descriptor table, appends the packed tail, then walks the
existing public cap marks to construct and pack the footer. Instruction-emulator
tests compare the complete raw-prefix/postpass result with pure packet encoding
for zero, maximal and random field values, empty packets, and up to 128 positions.
This postpass is not installed. Whole-controller execution/content refinement,
the packet-level inverse and the delivered checker remain unproved.
`ChainedFieldsFetch` and `ChainedRecordFetch` connect the typed record plan to
the standalone controller's actual instructions at words 9–2043. They prove
record-body execution in 2,035 cycles and zero public calls, with exact low-body,
descriptor and unread-input contents from a canonical raw source view. This
does not yet compose the outer loops or the cached raw prefix.
`ChainedTailAccess` derives traversal readiness and final-byte access from the
descriptor view and physical pointer ranges, including the zero-row case.
`ChainedRecordTailSetup`, `ChainedRecordPacking`, `ChainedTraversalFrame` and
`ChainedRecordFrame` compose actual standalone words 9–2066: complete low-body
construction, six-instruction setup and native tail packing. They prove exact
482-byte record output, source/output cursor advances of 498/482 bytes,
preservation of unread input and controller registers, zero public calls and
a 2,266-cycle upper bound under explicit canonical raw-input/range premises.
The next PC is word 2067, before the outer record-loop cursor/counter update.
`ChainedRecordControl` and `ChainedRecordIteration` add the actual scratch reset
and cursor/counter/BEQ/JAL updates. A complete single record iteration executes
in at most 2,273 cycles with zero public calls; its final edge is word 6 for
remaining records or word 2071 for the footer. This is not yet a record-count
induction or a whole-controller theorem by itself.
`ChainedRecordStream`, `ChainedRecordPrefix` and `ChainedRecordLoop` supply the
record-count induction, including zero records. From a canonical raw-stream
view and physical pointer ranges they prove actual standalone execution in at
most `2273*n` cycles, zero public calls, exact concatenated record bytes,
preservation of previously encoded output and the unread footer, and final
source/output advances `498*n`/`482*n`. Footer traversal and the cached raw-source
bridge remain open; this is not a whole-opener or delivered-machine theorem.
`ChainedFooterHeader`, `ChainedFooterFieldCode` and `ChainedFooterEmit` refine
the actual standalone footer field fragment at words 2085–2210. They include
the native two/six-bit width-selection branch, 29 low-byte copies, descriptor
stores and row-counter increment: 125 cycles for cap leaves or 126 internally,
zero public calls. The raw stride is 30 bytes. The generic `123*n` field-plan
cost is not the whole native footer cost. DFS mark traversal, old-prefix/mark
frames and final footer-tail composition remain to be connected.
`ChainedFooterLookup`, `ChainedFooterDescend`, `ChainedFooterInit`,
`ChainedFooterAdvance` and `ChainedFooterTailSetup` establish the actual
four-cycle mark lookup, occupied-node descent/pruning, seven-cycle footer
initialization from the record invariant, factored root/parent/sibling return
edges, and seven-cycle variable-count tail setup (including zero rows).
Their register/byte/word frames and actual fetches are proved. The recursive
subtree execution/content induction, preservation of marks through field
writes, whole footer-tail memory/execution composition, and cached-opening
raw-source bridge remain open.
`ChainedFooterFrame`, `ChainedFooterFieldStep` and `ChainedFooterMarks` supply
the missing field-write frames: old output and descriptor prefixes, unread
source, and every aligned mark word at `4096+8*node` for `node<512`. Word frames
are reconstructed from byte frames without importing a legacy artifact proof.
They extend the accumulated raw-field invariant through an actual footer emit
and preserve canonical marks through lookup, descent, pruning and return edges.
These frames alone do not establish whole-footer execution or the cached source.
`ChainedFooterReady`, `ChainedFooterLayout`, `ChainedFooterMoves` and
`ChainedFooterSubtree` now compose the actual recursive DFS, including empty
frontiers and pending siblings, with typed raw fields, canonical marks, exact
low output, descriptors, source advancement and return node/PC. All lookup,
descent, emission and return instructions are fetched from the standalone image.
Its exact recursive cycle count is bounded by `130*(2^(height+1)-1)`, with zero
public calls. The traversal is still not installed or connected to the cached
opening source, inverse packet machine, certificate or delivered artifact.
`ChainedFooterPayload` supplies the actual codec-derived raw-field layout.
`ChainedFooterTailReady` derives variable-row access safety from the completed
DFS memory view and a strict tail/metadata gap, including zero rows.
`ChainedOpeningFinish` proves the actual result-ABI instructions and successful
halt. `ChainedFooterComplete` composes root DFS, root decision, tail setup,
packing and halt, with exact encoded footer bytes and at most
`66448+13*frontier.length` cycles, under explicit typed-input, canonical-mark,
gap and encoding-fit premises. It is a standalone-image theorem, not delivered
certification. The following lemmas close numerical length/prefix readback and
record-loop/init composition; the actual cached-opening raw-source bridge remains open.
The strengthened `ChainedFooterComplete` now also preserves the complete old
packet prefix through tail writes and proves the numerical output cursor and
returned `x11` byte length, using `ChainedFooterTailFrame`. The proof-base ABI is
carried in `FooterReady`; the output-fit premise includes the prefix and base.
`ChainedRecordMarks` preserves every mark word through the entire record loop.
`ChainedFooterEntry` derives the complete footer invariant after record packing
and the actual footer initialization instructions. `ChainedPacketPacking` then
proves exact whole packet bytes, returned byte length and successful halt from
the nonempty record-loop entry (PC 4120), with at most
`2273*records.length+66455+13*frontier.length` cycles and zero public calls.
This theorem derives its tail gap and output-fit conditions from raw-memory
geometry instead of assuming them. `ChainedOpeningEntry` proves the actual first
five entry instructions and their nonempty-record readiness interface.
Canonical raw input and marks remain premises: neither the actual cached-opening
bridge nor empty-entry halt, installed-image relocation, inverse packet machine
or delivered certificate has been established by these standalone theorems.
The variable-width opener/checker, concrete accepted-trace extraction, delivered hiding/binding,
claim, certificate, and `Solution` have not been migrated. The old parent-image
proofs no longer describe the changed bytes. This branch is an uncertified
intermediate state, not a valid submission or a new verified score.

`ChainedCachedField`, `CachedBounds`, `CachedPayload`, `CachedGeometry`,
`CachedRecords`, `CachedFooter`, `CachedPacket`, and `CachedSource` reconstruct
the typed raw fields from cached words. In particular, `delivered_cached_packet`
uses `ChainedSerialization.delivered_physical_results` for the actual seeded
commitment: masked salts, the leaf sibling, all fifteen variable-width parents,
and the cap frontier give exactly the existing raw cached-opening serialization.
The generic conversion includes zero high widths and canonical zero padding.
`delivered_cached_source_view` turns that equality into the postpass `BytesAt`
view, conditional on the cached prefix's proof-byte readback contract. It does
not prove that a newly installed opener reaches that boundary, preserve its
mark table, or establish the entry registers. Empty-entry composition,
relocation/installation, packet inverse validation and delivered certification
still remain open.

`ChainedOpeningEmpty` proves the actual zero-count branch, its jump to the
length instruction and successful halt in ten cycles, without any memory writes.
`ChainedOpeningRun.native_opening_nonempty` composes the five entry instructions
with `native_packet_pack` from PC 4096, preserving its exact bytes, returned
cursor and numerical length, with at most
`2273*records.length+66460+13*frontier.length` cycles and zero public calls.
Both are standalone-image theorems; the nonempty case still requires the raw
source view, canonical marks and physical capacity at entry.

`PackedOpening.unpacked_opening_proof_layout` now factors raw cached-prefix
readback through `OpeningLayout`, completed record copies and footer reads,
without a full-image equality, fuel or packed-postpass assumption. The old ABI
theorem remains a wrapper for its existing callers. Consequently,
`ChainedCachedSource.delivered_cached_source_of_completed` obtains the canonical
raw source view directly from those copy facts and the actual seeded commitment
serialization. Executing the prefix under the replacement image and deriving
the controller's entry registers and marks still require separate proofs.

`PackedOpening.initial_mark_word_of_data_base` and
`initial_record_marks_of_data_base` similarly remove the old image equality
from mark initialization: image data must start at or above byte 8192.
`ChainedPrefixGeometry` derives raw-source/descriptor separation and controller
capacity from the ABI's concrete proof base for every position set. These are
initial-memory and geometry facts, not yet the complete entry-state invariant.

`ChainedPrefixInvariant` supplies state-predicate preservation across every
supported execution outcome, including faults and syscalls.
`ChainedPrefixControl` proves conservative direct successor PCs for ordinary
instructions. `ChainedPrefixTransport` derives actual fetch equality from equal
code prefixes and transfers supported unfinished runs, assuming the ordinary
prefix and suffix no-return invariants. This avoids any equality between the
old and new postpasses. Instantiating the no-return invariant and composing the
cached prefix with the installed controller remain unfinished.

`ChainedPrefixSuffix` now supplies the concrete old-opener no-return invariant
at PC 9836: kernel-checked decoding validates every suffix successor, fetch
bounds prevent syscall PC wraparound, and the prefix contains no `ECALL`.
`cached_prefix_replay` consequently transfers supported unfinished prefix runs
to any image retaining the first 1435 words, without assumptions about that
image's replacement postpass.

`ChainedCachedDispatch`, `ChainedCachedMarks`, and `ChainedCachedPrefix` now
instantiate that replay for the actual copied-record/footer execution, including
empty positions. `cached_prefix` reaches PC 9836 in exactly `scheduledCycles`
with zero public calls, the original count in x16, the raw source pointer in
x20, exact raw proof bytes, and all 512 canonical mark words. The zero mark is
proved preserved through the unrolled parent sweep rather than assumed.
These results require only `OpeningLayout`, initial data placement and matching
prefix bytes, not the legacy full `OpeningABI` or replacement-image equality.
Their relocated, installed-image composition follows below.

`ChainedDeliveredSource` connects the executed prefix to the actual delivered
seeded commitment's canonical typed raw records/footer. Its nonempty postpass
corollary discharges all native packing memory, marks, count, separation and
capacity premises from that boundary. It deliberately runs at the standalone
PC 4096 by changing only the boundary state's PC; it is not a claim about
installed execution at PC 9836.

`ChainedRelocationRun`, `ChainedSplicedFetch`, `ChainedControllerRelocated`, and
`ChainedCachedOpening` now compose the full opener at PC 9836 in the spliced
image. The proof covers empty and nonempty positions, all coin settings, exact
cached-prefix execution, successful HALT, canonical packet bytes and returned
length. Public queries contradict the proved zero-call run; a private syscall
at the controller's sole final `ECALL` advances past the image and cannot
succeed. `cached_encoded_length` identifies the output length with the approved
chained layout. Artifact equality is established below; the inverse/checker/
security chain remains unfinished.

`ChainedOpeningArtifact.opening_manifest_image` now proves exact equality of
the official generated opening image and the cached-prefix/controller splice.
`artifact_cached_opening` proves exact empty/nonempty opening execution from
the delivered seeded commitment, for any fuel of at least the scheduled cached
prefix plus the proved postpass cycles, with exact bytes and returned length.
`cached_encoded_length` identifies that length with the chained layout, whose
pure bound is **65,472 bytes** for at most 128 positions.
`ChainedOpeningDelivered` connects that execution to the actual
`Submission.run` and `readProof` through an abstract initial-state/fuel lemma:
for 128 positions the installed opener succeeds with zero public calls in
at most **444,579 cycles**, returning the exact canonical packet of at most
**65,472 bytes**. This is an opening-only result, not a certificate.
The opening bytes in `programs.json` are generated from the checked literal
images, preserving words 0–1434 and installing the controller at word 1435.
The checker, certificate, claim and `Solution.lean` still need migration; these
opening results are not an official certified score.

`ChainedTailParseBits` proves inverse-row extracted field bits and exact scratch
byte writes. The inverse-row memory frame uses projected `getMem` equations,
leaving recursive state functions opaque; whole-packet inverse refinement and
the installed checker's accepted-trace proof remain unfinished.

`ChainedTailParseBuffer`, `Plan`, `Source`, `Memory`, `Result`, `Access` and
`Execution` refine the inverse rows against an independent byte-stream plan
for arbitrary width lists bounded by six. The plan proves exact field widths,
consumed bytes and bit conservation; native scratch writes preserve unread
source bytes and width metadata. `native_parsed_rows` derives memory-access
and counter/branch readiness from physical ranges, then executes the actual
inverse-row instructions through validation, in at most **17*n+3 cycles**
and zero additional public calls, starting after the entry branch. Its flag
is one exactly when the supplied length matches consumption and all remaining
padding bits are zero. Kernel examples cover empty and mixed-width plans,
valid padding, short/long supplied lengths and nonzero padding. These are
supporting row results: native whole-packet low-body reconstruction and the
strict checker controller have not been implemented or installed.

`ChainedInverseRows`, `BitStream`, `Decode` and `DecodeParts` connect parsed
scratch rows to the generic codec's typed decoder, recover its unchanged low
bytes and account for exactly the consumed input bytes. `ChainedInversePrefix`
proves that unread bytes cannot affect parsed fields, residual bits or cursors.
`ChainedInverseCanonical` proves strict codec acceptance from the native
length/padding conditions and the supplied input-byte view, for arbitrary
aligned width specifications bounded by six.

`ChainedInverseFieldTail`, `Field`, `FieldFrame`, `FieldsReady`, `FieldsMemory`,
`FieldsExecution` and `Payload` reconstruct complete raw payloads from low
bodies and parsed descriptors, with actual execution in **4*L+6*F cycles** and
zero additional public calls. The proof preserves previous output and unread
input, using disjoint source/output/scratch ranges and opaque recursive state
equations. Reconstruction preserves configured padding in the output workspace;
the checker must establish that its raw-record padding starts at zero.
`ChainedParsedMetadata` proves exact descriptor readback after inverse parsing
and projected register frames. These are compositional payload results, not an
installed record/footer decoder or strict checker controller.

`ChainedParsedPayload` connects the native parser's acceptance flag to strict
`unpack`/`decode` and establishes exact descriptors for the reconstructed payload.
`ChainedInverseFetch` compiles abstract inverse fetch premises from instruction
shapes independent of payload values. `ChainedInverseRecordCode` supplies a
**2,018-word** component image, proves every instruction's decoding and complete
raw-record reconstruction execution in **2,018 cycles**, zero additional public
calls, under the source/output/metadata readiness and zero-padding premises.
Its cursors consume **479 low bytes**, produce **498 raw bytes** and consume
**34 descriptor bytes**.

`ChainedInverseFooterCode` supplies a decoded **123-word** component image with
a variable-count loop for **29 low bytes plus one parsed high byte per node**.
`ChainedInverseFooterControl`, `Run`, `Memory`, and `Entry` prove its complete
variable-count execution and raw-memory refinement. The entry and loop take
**1 + 122*n cycles**, zero additional public calls, and advance source/output/
metadata by **29*n / 30*n / 2*n**, with zero remaining nodes. Zero-count entry
takes one cycle without accessing any buffers, including invalid buffer pointers.
The memory theorem reconstructs typed raw fields from initialized low bodies and
descriptors, preserving previous output, unread source and descriptor suffixes;
it assumes 29-byte lows, no field padding, unit output stride and the existing
source/output/scratch separation. PC projection uses a generic branch-offset
lemma before specializing the backward jump; state iteration remains opaque
behind zero/successor equations. Neither inverse component is installed in the
delivered checker, and record/footer parser/controller composition remains
unfinished.

`ChainedInverseFooterPayload` instantiates the memory result with the actual
`InteriorCodec.footerSpec` and `footerRawFields` payload layout. This still
requires initialized source bytes and parsed descriptors; it does not establish
strict packet-controller execution or checker acceptance refinement.

`ChainedWidthInit`, `WidthTable`, and `WidthTableRun` construct trusted odd-byte
width tables in exactly **3 cycles per row**, without reading memory. They prove
exact instruction decoding, fetches, execution, metadata cursor movement,
register frames, and preservation of even descriptor bytes and all bytes outside
the written odd slots. Recursive state construction is opaque behind explicit
empty/cons equations. `ChainedRecordWidths` specializes this to the actual
**17-row / 51-word** record table, including the six zero-width parent rows.

`ChainedFooterWidths` supplies a decoded runtime selector and metadata store:
**2 high bits at cap leaves / 6 internally**, taking **5 / 6 cycles** respectively.
It preserves all memory except the selected odd metadata byte and establishes
unit output stride for the inverse footer. `ChainedRecordParseSetup` connects
initialized tables to the strict parser acceptance theorem, preserving its input
bytes and residual buffer under explicit separation premises. Acceptance implies
strict record decoding and exactly **482 supplied bytes**. Initial source bytes,
empty buffer, declared end pointer and separation still need derivation by the
packet controller.

`ChainedPacketBounds` proves exact accepted packet length, complete 482-byte
record slices and their three-byte tails, empty-packet rejection of trailing
data, and the global source bound **below 2^33 bytes**. The bound
`482*positions.card + 3776` applies to all position counts: **65,472 is the scored
128-leaf bound, not a global ABI limit**. These modules do not yet implement the
public-position mark traversal, record cursor/padding setup or whole packet
controller. No chained checker installation or accepted-trace theorem is claimed.

`ChainedPacketControllerCode` supplies a standalone **2,367-word** strict decoder
using the checking ABI. It checks the record envelope, handles empty input before
buffer access, builds public-position marks, constructs record/footer width
tables, parses canonical tails, zeros record padding and reconstructs raw records
and footer bytes. Raw output starts at `proof+2^33`; metadata is reserved at
`2^35`. On successful decoding it restores the input root/position/value/count
registers and returns the raw buffer in x15/x17 before a successful halt.
`ChainedPacketControllerFetch` proves exact instruction decoding and fetches,
including the placements of both parsers and inverse components. Whole-controller
execution/content refinement and physical ABI workspace derivation are not yet
proved.

Local literal-image interpreter tests cover canonical zero/max/random packets,
the scored boundary, larger unscored batches, an empty footer, malformed lengths,
nonzero footer padding and trailing bytes. These are not official VM checks.
**This decoder performs no cryptographic authentication and is not installed as
the checker.** A canonical packet with changed leaf data still decodes; chained
oracle/path checking and concrete `AcceptedTraceRefines` remain necessary.

`ChainedCheckerControllerCode` adds concrete **3,012-word** cryptographic checking
bytecode after the decoder. It retains the pinned two-permutation leaf and DFS
control instruction templates, bypasses the legacy unpackers and replaces every
parent compression site with the actual chained packing/continuation routines.
Lower heights use the approved variable call/width schedule; cap heights use one
call and 238 bits. Parent wrappers preserve the checking control registers and
canonicalize both 238-bit seed children. The decoder's marks are cleared before
authenticated cap collection. `ChainedCheckerControllerFetch` proves exact whole
image decoding/fetch and the placements of all parser, inverse and hashing blocks.

Local deterministic toy-oracle interpreter tests accept sparse reference paths,
including the 65,472-byte boundary, and reject altered values, nonces, siblings,
footer nodes and roots. Malformed packets are rejected before public calls; empty
input avoids buffer access. These tests are neither full-message commitment
completeness nor official VM verification. **The cryptographic checking image is
installed but not yet certified:** execution/content refinement, concrete
`AcceptedTraceRefines`, delivered security and the certificate migration remain.

`ChainedCheckerArtifact.checking_manifest_image` proves exact equality with the
officially rendered checking bytes. The generated manifest changes only that
image; the ABI, fuel and other images are unchanged. A local delivered-byte
opener-to-checker regression accepts matching sparse cached trees, including the
scored boundary, and rejects tampered data and trailing bytes. It does not execute
the full seeded commitment and is not the official VM verifier.

`ChainedCheckHashState/Run/Content/Delivered` refine the actual lower and cap hash
call sites through both subroutine returns. Opaque state functions have projected
register/memory/PC frames. Under explicit prepared-state, counter and access
premises, the exact delivered checking image takes
`34 + continuationInstructions remaining` instructions,
`41 + continuationCycles remaining` cycles and `remaining + 1` public calls.
The projected output program is exactly the canonical first query, full-width
continuation queries, then one final truncation, including zero continuation
calls. This does not yet derive those premises from wrapper setup or whole-check
execution and does not establish `AcceptedTraceRefines`.

`ChainedCheckerGeometry` proves the public-region ordering and capacity/separation
of the encoded packet, raw reconstruction and metadata workspaces for all
admissible position counts. `ChainedCheckerEmpty` proves the exact installed
checker's zero-position, zero-length execution: **21 cycles, zero public calls**,
from an abstract entry state with arbitrary buffer pointers.
Its all-word/all-byte preservation frames use abstract branch targets and an
abstract jump offset before specializing the delivered instructions.

`ChainedCheckerRecordSetup/RecordReady` compose the actual record-loop instructions
at words **57–114**: metadata-pointer reset, all seventeen trusted widths and
parser register setup, in **58 cycles, zero public calls**. They derive the empty
parser buffer, seventeen-row count, three-byte tail endpoint and initialized
width table, and preserve the tail input under the proved workspace separation.
The entry PC, metadata pointer, source-pointer range and initial source-byte view
remain explicit premises.

`ChainedCheckerRecordParseState/ParseRun/Parsed/Readback/ParsedFrame` now compose
the actual parser through word **136**, including strict codec acceptance,
descriptor readback, preserved source bytes and control-register frames. Input
bytes are read from the actual initial state; a 482-byte record consumes exactly
three tail bytes with no residual padding bits. The parser's trusted widths make
every such record syntactically decodable; cryptographic authentication is later.

`ChainedCheckerRecordPadding/RawPadding/ReconstructionEntry` prove the actual
accepted-record branch, source/metadata reset and both raw padding stores.
Initialization through word **142** takes **at most 356 cycles, zero public
calls**, with source/output/metadata pointer projections and every required raw
padding byte initialized. State functions remain opaque; an abstract-state PC
byte-frame lemma avoids expanding the full parsed state.

`ChainedCheckerRecordInverseReady/InverseRun` derive the inverse body's physical
readiness from actual word-142 source, descriptor and padding contents. They
compose all **2,018 inverse instructions**, reconstruct the exact typed raw
record, advance source/output/metadata by **479/498/34 bytes**, and reach word
**2160**. Initialization, parser, padding and inverse execution together take
**at most 2,374 cycles, zero public calls**, starting at word 57 with explicit
source/output/metadata geometry and a 482-byte source view.

`ChainedCheckerRecordInverseFrame/Advance/Iteration/Stream/Loop` compose the
actual source advance, count decrement and back/exit branches into record-count
induction. Given `CheckerRecordStreamReady`, the installed decoder writes the
exact concatenated raw records, preserves previous output and the unread footer,
advances source/output by **482/498 bytes per record**, exhausts the counter and
reaches footer word **2164**, in **at most 2,378 cycles per record, zero public
calls**. The zero-record model is the already-reached footer boundary, not a new
empty-ABI entry proof. Arbitrary-byte and register frames cover untouched memory
outside the raw output and 34-byte metadata scratch region.

`ChainedCheckerRecordUntrusted` proves every 482-byte record is the encoding of
its typed decode, partitions any sufficiently long supplied byte stream into
those records and the unread footer, and instantiates the loop invariant from
that arbitrary source view. No cached-tree origin or honest-record assumption
is needed for this decoder step.

The public count and source/output/metadata entry facts are still not derived
from full ABI entry. Footer traversal/parsing/inverse composition, complete ABI
invariants and accepted cryptographic traces remain uncertified.

`ChainedCheckerFooterInit/Width/Lookup/Control` refine the actual footer control
primitives. Record exit composes with four initialization instructions to reach
word **2168**, retaining the raw records and unread footer. Lookup reads marks
through **x4** and takes **four cycles**. An unmarked node writes its trusted
width and increments the row count in **seven cycles internally / six at cap
leaves**. Marked-node descent/pruning and root/parent/sibling return edges have
exact installed-image execution and register/memory frames. These are component
proofs, not yet whole-footer parsing/inversion.

`ChainedCheckerFooterReady/Moves/Subtree` compose these edges recursively over
the height-eight cap. `checker_footer_widths_complete` reaches word **2190** in
**at most 7,407 cycles**, with the exact cap-frontier width table, row count and
metadata cursor. It preserves canonical marks, all bytes outside the 512-byte
footer scratch interval and every non-work register. Empty subfrontiers and
marked cap-leaf pruning are included. Initial mark/count/cursor premises remain
explicit; the following conditional components cover parser setup and parsing.

The inverse-copy byte-frame helper has a distinct name from its forward
counterpart, allowing opener and inverse-decoder proof modules to coexist.

`ChainedCheckerFooterSetup` refines actual words **2190–2201**. It computes the
29-byte low-body endpoint, saves the footer count, guards that endpoint against
the supplied proof end, initializes the parser buffer/metadata pointer, and
reaches word **2202 in eleven cycles** on the guarded path. Short low bodies
reach the reject jump at word 2198. Register/memory frames and the natural-number
characterization of this guard are proved.

`ChainedCheckerFooterParseState/ParseRun` refine the empty/nonempty branch at
word **2202**, variable-row parsing and validation through **word 2223**. Physical
readiness comes from the trusted width table, actual entry memory and explicit
source/metadata geometry. Parsing takes **at most 17*n+4 cycles**, or
**17*n+15** including setup, with zero public calls. The empty-row branch is
included. The native flag exactly enforces tail length and zero residual padding.

`ChainedCheckerFooterParsed/Readback` connect that flag to strict
`unpack`/`decode` for `InteriorCodec.footerSpec`, derive the low-body length guard
from the supplied endpoint, and prove exact descriptor bytes. They preserve the
supplied source bytes and inverse-entry registers, including the saved row count.
These statements apply to arbitrary supplied bytes, not only honest openings.
`ChainedCheckerFooterReconstructionEntry/InverseReady/InverseRun/Complete` compose
the accepted branch, pointer/count resets and actual inverse through **word 2352**.
`checker_footer_decode_complete` proves strict footer acceptance, exact raw footer
bytes appended to the preserved record prefix, source/output/metadata advances
of **29/30/2 bytes per row**, exhausted counter, and **at most 139*n+21 cycles**
from word 2190, zero public calls. Empty footers are included. Initial width-table,
ABI, source/output separation and accepted-parser premises remain explicit.

`ChainedCheckerFailure` refines the actual rejection halt and footer rejection
edges: short low bodies reject in **12 cycles** from word 2190; invalid length or
padding flags reject in **five cycles** from word 2223. The parser flag is always
zero or one, and strict-codec rejection forces zero under the physical premises.
`ChainedCheckerRestore` proves the four saved-register loads, raw proof pointer
and length setup, and nonempty dispatch from **word 2352 to word 2367**, in
**nine cycles, zero public calls**. It preserves all memory and restores root,
indices, values and count from the actual saved words. The metadata pointer and
nonzero saved-count premises remain explicit.

`ChainedCheckerFooterFrame` bounds footer reconstruction writes to its raw output
range and parser descriptor bytes, and preserves non-work registers, including
the metadata and raw-buffer bases. `ChainedCheckerSavedSlots` defines the four
saved words as an invariant against a fixed original ABI state. It carries that
invariant through the record loop, footer initialization, width DFS and footer
parser/inverse, then proves restored **x11/x13/x14/x16 equal the original ABI
registers** and discharges restoration's nonempty-count premise from the original
count. The preservation statements do not assume honest proof bytes.

`ChainedCheckerSave` splits actual words **18–23** into two metadata arithmetic
instructions and four stores. Each SD is characterized at one queried word,
without unfolding the arithmetic state. It proves that all four saved words
equal their source ABI registers, preserves other words and non-x8 registers,
and executes the installed save block in **six cycles, zero public calls**,
ending at word 24. Transport from the original entry through admission and the
remaining mark prefix is completed incrementally below.

`ChainedCheckerAdmission` proves the installed successful nonempty length guards,
derives those guards from **482*n ≤ length ≤ 482*n+3776** for every ABI count
`n ≤ LENGTH`, and establishes the raw base and preservation of original ABI
registers. Entry through the four saves reaches word 24 in **19 cycles** with
the original ABI words in their actual metadata slots.
`ChainedCheckerMarksClear` and `ChainedCheckerClearRun` compose mark initialization
and all **512** zeroing iterations. Actual entry reaches **word 32 in 2,071
cycles, zero public calls**, with all mark words zero, metadata/mark bases set,
original ABI registers preserved and the saved-slot invariant established.
Frames preserve memory outside the mark table and four saved words. Leaf seeding
and the descending parent sweep still need integration before decoder entry 57.

`ChainedCheckerSeedState`, `ChainedCheckerSeedRun` and `ChainedCheckerSeedStream`
prove the installed leaf-seeding loop at words **35–43**. With explicit typed
public-index words, count, aligned input span and mark-base premises, it executes
in **9*n cycles, zero public calls** and writes exactly the cap groups in those
positions (duplicates are idempotent). It preserves every other mark word,
unrelated registers/memory and the four original ABI slots; the empty stream
performs no accesses. The three-instruction setup from word 32, actual loader
instantiation and parent sweep remain to be composed.

`ChainedCheckerInput`, `ChainedCheckerSeedInit` and `ChainedCheckerSeedEntry`
instantiate the public-index premises from the **actual delivered loader**, for
arbitrary proof bytes and positions. They compose admission, saves, all clears,
setup words32–34 and the entire leaf-seeding loop in **2074+9*n cycles, zero
public calls**. Exact leaf marks and original saved ABI words are established
without a prepared-index-memory assumption. The parent sweep and final pointers
remain before record entry57.

`ChainedCheckerParentState/Run/Sweep`, `ChainedCheckerMarkBoundary/Input`
and `ChainedCheckerRecordInput` now compose **the actual delivered nonempty
entry through word57**, in **4627+9*n cycles, zero public calls**. The installed
descending sweep establishes canonical occupancy for all512 nodes, including
the unused node0 and all cap leaves. The final copies are x18←x15 and x6←x12
(encoded source and raw output), as checked against the delivered opcodes.
Original public registers and saved x11/x13/x14/x16 slots, metadata/raw pointers,
and pointwise memory outside marks/saved slots are proved from the actual
loader. Admission length bounds remain explicit; no honest-proof or prepared
public-memory premise is used.

`ChainedCheckerInputProof`, `ChainedCheckerRecordsDelivered`,
`ChainedCheckerDecodedMarks`, `ChainedCheckerFooterInput` and
`ChainedCheckerDecodedInput` compose the actual supplied bytes through the
whole nonempty decoder. For arbitrary packets within the admission length
bounds, execution either rejects or reaches cryptographic entry **word2367**
in **at most 47652+2387*n cycles, zero public calls**. This includes empty
footers, short-body rejection and invalid length/padding flags. The successful
boundary has exact decoded records/footer, canonical footer acceptance,
restored original x11/x13/x14/x16, raw pointer/length and preserved host public
memory. It has no prepared decoder-memory or acceptance-flag premise.

Hash integration, accepted cryptographic traces, delivered security and
certificate migration remain open. No complete delivered certificate is claimed.

`ChainedCheckerCryptoEntry` proves actual execution from **word2367 to word2395**
in **2072 cycles, zero public calls**: fresh clearing of all512 occupancy words,
both raw-record/nonempty guards and the seventeen-instruction record setup.
The guards are derived from `CheckerDecodedInput`, not assumed. Raw decoded
bytes, original public ABI and public memory survive; all occupancy words are
proved zero. Composition from the initial loader either rejects or reaches
this boundary in **at most 49724+2387*n cycles** under the existing header bounds.
The setup state remains opaque. Its fourteen assigned register getters are now
proved by last-write projection and suffix frames, with short two-instruction
groups for x3/x4/x24; no whole seventeen-step state or scalar-fold reduction is
needed.

`ChainedCheckerRecordPath` verifies all six installed nonce/sibling/frontier
halfword-copy sites (8, 15 or 16 halfwords), including execution, PC, register
frames, exact destination bytes and byte frames outside the destination. The
copy results require physical `CopyReady` premises; only the first nonce copy
has those premises derived from `CheckerDecodedInput`. Short last-write header
getters establish the actual first sorted public index and its position tag.

`ChainedCheckerLeafRun` composes the delivered first leaf through **word2432**
from word2367: **2109 instructions, 2123 cycles and two public calls**. Both
permutation queries have the pinned two-permutation leaf layout; recorded query
rows, output digest, final PC and register/memory frames are proved. The first
leaf readiness is derived from the decoded ABI, not a prepared-state premise.
`ChainedCheckerLeafData` identifies the message window with the caller's first
sorted dependent value and the nonce bytes with the decoded record's 121-bit
nonce, zero-extended to128 bits. Its typed query rows and leaf digest require
no honest-record, cached-tree or prepared-memory premise.

`ChainedCheckerLeafReturn` executes the delivered word2432 jump, nonce advance,
238-bit mask and lower setup. It reaches **word2437** from word2367 in
**2120 instructions, 2134 cycles and two public calls**. The masked digest,
raw cursor+16, leaf node, sixteen-level counter, scratch pointers and public
selector/size are derived from the decoded input. The delivered path boundary
is opaque; register and memory facts are projected separately.

`ChainedCheckerLower` executes both first-sibling ordering branches from
word2437. It derives sibling-copy readiness from the decoded path boundary,
copies the sibling and current digest into their actual left/right slots, and
calls the lower wrapper. `ChainedCheckerHashWrapper` executes all31 actual
register saves, both child masks, the first-height schedule and public hash ABI
setup. At word2817 it derives `LoopArgs`, valid input accesses, height0, three
continuation calls and the234-bit final mask; these are not prepared-state
premises on the composed execution theorem. The shared saves and child-mask
execution are also recognized at the cap wrapper, but its schedule is not
yet composed.

The composed theorem reaches **word2820**, immediately after the lower hash,
in **165 instructions / 193 cycles** for an even leaf node or
**166 instructions / 194 cycles** for an odd leaf node, with **four public
calls** from word2437. From word2367 the respective totals are
**2285 / 2327 / six** and **2286 / 2328 / six** (instructions/cycles/calls).
The actual query trace and resume PC are proved. The child-value linkage below
completes the first-level content premises.

`ChainedCheckerHashRestore` and `checker_first_lower_execution` now compose
result-copy/register restoration at words2820–2860, the238-bit return mask and
the cursor/node/count transition back to **word2437**. The first full lower
level takes **216 instructions /244 cycles** for an even node and
**217 instructions /245 cycles** for an odd node, with **four public calls**.
The raw cursor advances32 bytes, the node shifts right once and the counter is15.
The shared result-copy and31-register load/return code is also recognized for
the cap wrapper. `ChainedCheckerLower` links all eight prepared input words
to the parity-ordered current digest and decoded first sibling. It proves the
delivered wrapper's two top-word masks, including arbitrary high padding bits,
and instantiates `checker_hash_content` with the actual ordered pair. The sibling
is the 238-bit second field of the untrusted decoded record, preserved through
leaf execution; the current child is the actual masked leaf reply. Both parity
branches are covered without prepared child-memory premises.
`ChainedCheckerLower` now proves the actual schedule and hash-wrapper
execution for every lower height0–15, including the exceptional height8 and15
branches. It derives height, remaining calls, final mask and source/ABI premises,
recognizes each fetched instruction, preserves saved words and instantiates
canonical hash content from the actual child buffers. Cap DFS, whole-check hash
premises at word2915, accepted-trace refinement and delivered security/certificate
migration remain unproved.

`ChainedCheckerLower` proves the later-height dispatch, both actual30-byte
sibling copies, their two zero-padding bytes, current-child copies and jumps
back to word2606. Under height-indexed loop-head premises, each branch takes45
instructions/cycles and no public calls. It also proves the general cursor,
node and counter transition after restoration, including the height15 fallthrough
to word2614.

`ChainedCheckerLower` composes all16 actual lower levels by induction and
reaches **word2614**, with exhausted lower counter, raw cursor at the498-byte
record boundary and node shifted right16 times. It transports the actual31
saved registers through each hash return and derives each next loop-head state;
the induction includes the empty suffix. From word2437 the totals are
**3654 instructions /4284 cycles /90 public calls** for an even initial node,
or **3655 /4285 /90** for an odd one. Composed from the decoded word2367 entry,
the first leaf and complete lower path take **5774 /6418 /92** or
**5775 /6419 /92**. The lower modules are consolidated in this single file,
freeing five submission entries. The file also proves preservation of the11
fixed record/cap ABI registers and aligned words outside the low hash scratch
and lower-path working buffers, through all16 levels. This includes occupancy
marks, heap roots and raw input. Byte/buffer frames transport high proof/public
regions, including empty buffers. Later decoded-field content, the outer record
loop and cap execution still require integration.

`ChainedCheckHashLowFrame` proves directly that every supported trace at either
hash site2817/2915 preserves all31 saved words at addresses0–240. It follows
the packer's stores256–312, public reply writes256–287, continuation header/tail
stores288–312 and final mask store280; it does not use `OutsideScratch` or a
heap-address lower bound.

`ChainedCheckerCapSchedule` proves the installed cap-height controller from
**word2901 to word2910**, under an explicit parent-node/height interval and
entry PC. Its actual shift/decrement loop derives heights16–23, zero
continuation calls and the canonical238-bit final mask. The cost is exactly
**7+4*(7-height) instructions/cycles, zero public calls** (7–35 cycles).
It preserves all memory and every register outside x16/x17/x18/x30, including
the empty loop for the root parent. This is a separate delivered-code component,
not yet connected to cap DFS or whole-check acceptance.
`ChainedCheckerHashWrapper` also generalizes child-mask execution to arbitrary
source addresses with explicit validity of both accessed top words; the original
lower-buffer specialization is retained.

`ChainedCheckerCapHash` derives the actual cap wrapper's31 saved-register
stores, heap-child mask access, height schedule and hash ABI from word2861.
Under explicit caller PC, parent interval and child-heap pointer premises,
word2915 has `LoopArgs`, valid child reads, the derived canonical height,
zero continuation calls and the final mask. Preparation costs
**52+4*(7-height) instructions/cycles, zero calls**. The actual public hash
reaches **word2918** in **91+4*(7-height) instructions,
98+4*(7-height) cycles and one public call** from word2861. Canonical query
content is proved under explicit prepared child-word premises. The caller
premises still need derivation from cap DFS.

`ChainedCheckerCapReturn` generalizes result-copy execution and saved-word frames
to an arbitrary64-bit destination with four valid accesses and explicit
saved-word separation. Abstract LD/SD guard lemmas keep instruction execution
separate from delivered-image fetch proofs. Instantiation at the parent heap
address proves cap restoration through word2958 and return to **word2714**,
under the explicit saved caller-link premise. From word2861 this costs
**132+4*(7-height) instructions,139+4*(7-height) cycles and one public call**.
All31 nonzero caller registers are restored; the snapshot words remain saved
values, not the pre-wrapper scratch contents. Cap DFS, child heap-content
linkage and the outer record loop remain to be composed.

`ChainedCheckerCapParent` proves actual words2708–2713: halving the completed
right-child node, calculating both heap pointers and installing the caller
link. It derives the wrapper PC2861, source/destination pointers and return
link2714 from the right-child coordinate and fixed heap base. Parent ranges
follow from the typed cap-subtree span. With that range, the composed call
from2708 returns at2714 in **138+4*(7-height) instructions,
145+4*(7-height) cycles and one public call**. This is a parent-call component,
not yet a whole-DFS theorem.

`ChainedCheckerCapFinish` proves the actual post-wrapper jump, final238-bit
mask and back edge to **word2704**. The complete parent component from2708
therefore costs **145+4*(7-height) instructions,152+4*(7-height) cycles and
one public call**. The fixed heap base and completed right-child coordinate
remain explicit, as does the typed parent range; lookup, frontier traversal
and recursive DFS entry still need composition.

`ChainedCheckerCapVisit` proves delivered mark lookup, marked-leaf pruning and
left descent at words2661–2667, with costs4/5/7 instructions/cycles and no
public calls. Fetch proofs use the installed chained image; the packed
controller's corresponding pure instruction/pointer algebra is mirrored with
the delivered PCs. Memory and unrelated registers are preserved. This lookup
component is not yet the recursive cap DFS.

`ChainedCheckerCapFrontier` instantiates the actual **36-instruction/cycle,
zero-public-call** frontier reader from word2668 to2704. It establishes the
exact30-byte heap digest with two zero padding bytes, cursor+30, register
frames and memory preservation outside the selected32-byte heap slot. Its
premises are physical node/source bounds, even alignment and the delivered
remaining-length guard; no prepared child-content premise is used for this
frontier copy. Recursive cap traversal and parent child-content linkage remain
uncomposed.

`ChainedCheckerCapAdvance` supplies the delivered three-step cap initialization
at2658, two-step root/parity decisions at2704/2706 and two-step right-sibling
advance at2716. It also proves that the complete parent trace returns the
typed parent coordinate and restores every saved nonwork register (including
the heap, marks and footer controls). These are scalar/control components;
the parent trace's mark/raw memory frame and recursive DFS composition are
still outstanding at that component boundary.

`ChainedCheckerCapFrame` now proves the complete parent trace preserves aligned
words outside scratch and the cap heap, including all marks and the public/raw
buffers. It composes the actual snapshot, child masks, height schedule, hash,
heap result copy, restoration and final mask. Negative JAL memory projections
use an abstract immediate lemma, avoiding concrete sign-extension reduction.
The remaining recursive DFS needs these frames and the scalar components
assembled into its traversal invariant; no whole-DFS claim is made here.

`ChainedCheckerCapPosition` transports the canonical mark/ABI and typed
heap/cursor position through lookup, frontier reads, sibling advance and parent
ascent. The right-child `CapSpan` now derives the caller PC, parent range and
heap controls for the actual parent call: **word2704 →2704**, in
**149+4*(7-height) instructions,156+4*(7-height) cycles,one public call**.
Sibling advance from the left return costs six ordinary cycles. These typed
transition lemmas are not yet assembled into the recursive cap traversal or
outer record loop.

The cap node/shift threshold proof now uses division and monotonicity of powers,
without its former heartbeat override or finite case enumeration.

`ChainedCheckerCapDfs` defines the height-recursive delivered control trace and
its exact instruction/call specification. The marked-leaf terminal case takes
five ordinary instructions; the unmarked frontier case takes forty. Both now
prove execution, exact cursor progress, typed cap position and external memory
frames.

`ChainedCheckerCapWalk` now proves the full height-eight control/resource
induction, including both recursive children, sibling advance and the actual
parent hash/return. From a typed canonical-mark position at **word2661**, it
returns to **word2704** with the same heap node, exact frontier cursor advance,
fixed ABI and external-memory frames. Parent caller PC/range/pointers are
derived inside the induction. Uniform cap bounds are **58,690 instructions,
60,475 cycles and255 public calls**. Initial cap marks/ABI still need derivation
from the outer record loop; chained hash semantic content and accepted-trace
refinement are separate outstanding obligations.

`ChainedCheckerCapEntry` composes the actual initialization at **word2658**,
the height-eight traversal and the root-return branch into **word2718**, the
commitment-check entry. It establishes the configured parent ABI from the
three initialization instructions, preserves the original claim pointer and
external memory, and advances by exactly30 bytes per frontier node. Bounds
including those five control instructions are **58,695 instructions,
60,480 cycles and255 public calls**. Canonical incoming marks, heap/control
bases and a sufficiently long reconstructed footer remain explicit premises.

`ChainedCheckerCapRoot` proves the actual suffix at **word2718**: raw-cursor
equality, all four root/claim word comparisons, and success/failure ECALLs at
**words2733/2740**. Within a sixteen-instruction budget it terminates with zero
public calls; success is equivalent to exact raw consumption and equality of
the heap root with the claimed32-byte commitment. This is a delivered-image
control/data comparison theorem, not yet authentication of that root by the
typed input's full chained opening paths.

`ChainedCheckerCapMarks` proves the descending **255-parent** OR sweep at
**words2647–2657**, canonical internal marks from the incoming leaf marks,
register/memory frames and composition with the entire delivered cap traversal.
It reaches **word2718** within **61,246 instructions,63,031 cycles and255 public
calls**, with exact frontier consumption. The sweep alone takes **2,551 cycles,
zero public calls**. This consolidates three mark proof layers into one module,
without retaining their old heartbeat overrides. Incoming leaf marks still
need connection to actual successful record insertion/deduplication.

`ChainedCheckerRecordFinish` proves the actual **word2614** group-root
insertion/deduplication and outer-record latch: fresh roots are copied and
marked; repeated groups must match all32 bytes or branch to rejection.
Successful records advance the index/value pointers and decrement the count,
reaching **word2647** after the last record or **word2396** for the next one.
The component takes at most **23 ordinary cycles/instructions,zero public
calls**, under explicit node/counter/heap premises. Seven code/view proof
layers are consolidated into one new-image module without heartbeat overrides.
Raw-base-relative lower readiness is established below; repeated-record setup
at2396 and the complete outer loop remain uncomposed.

### Chained module consolidation

The checker proof now consolidates55 single-consumer intermediate modules
into11 existing consumers, preserving public declaration names and each
original module's local options/attributes in separate sections. Private
helper names are prefixed to avoid collisions. No machine bytes or claims
change. The merged groups are:

| Consumer | Absorbed modules |
| --- | ---: |
| `ChainedCheckerRecordInverseRun` |12|
| `ChainedCheckerDecodedInput` |16|
| `ChainedCheckerRecordUntrusted` |4|
| `ChainedCheckerFooterControl` |3|
| `ChainedCheckerSavedSlots` |3|
| `ChainedCheckerFooterComplete` |7|
| `ChainedCheckerCapVisit` |2|
| `ChainedCheckerCapRoot` |3|
| `ChainedCheckerCapPosition` |2|
| `ChainedCheckerFooterSubtree` |2|
| `ChainedCheckerClearRun` |1|

### Record-relative lower paths

`CheckerFirstPathReady` now carries a record ordinal and a bounded, even raw
record base. `CheckerLaterPathReady`, `CheckerLowerLoopReady` and
`checkerLowerCursor` carry that base through all 16 lower levels, including
the instruction/cycle/call bounds and register/heap frames. Their default
arguments preserve the first-record interface. `checkerRecordBaseAt` uses
the decoder's 498-byte raw-record stride, also established by
`record_raw_fields_length` and the record-stream pointer theorem.

The generic first-child byte frame does not require 8-byte alignment: later
record bases are only 2-byte aligned. `checker_record_path_ready` derives the
word 2437 postcondition from arbitrary prepared `LeafReady`, raw pointer,
loaded public index, length and pair-buffer premises. The lower induction
then reaches word 2614 in 3654/3655 instructions, 4284/4285 cycles and 90 calls.

`CheckerRecordCoreReady` and `checker_record_core_path_execution` cover actual
repeated-record setup at2396, nonce copying, both leaf calls and the mask return
through2437 in47 instructions,61 cycles and2 calls. The generic
`checker_record_lower_execution` then reaches2614 in3701/3702 instructions,
4345/4346 cycles and92 calls, advances the raw cursor by498 and derives the
cap-group node from the selected public index. Fixed-register frames now also
preserve the leaf tag base, nonce scratch pointer and tree length for the next
record. Message/index/raw-pointer and buffer-geometry premises remain explicit.

`checker_record_group_ready` derives insertion/deduplication readiness from
that trace, the incoming remaining counter and root/mark bases. The delivered
tail then either rejects, loops to2396 or reaches2647; its separate bound
remains at most23 cycles and zero calls. These are per-record components, not
an outer-record induction or a full-checker theorem.

Per-record buffer frames now preserve unaligned buffers outside the active
message window and extend through insertion/deduplication. Under the successful
nonlast-record branch, `checker_record_next_ready` derives the next leaf entry,
raw base advanced by 498 bytes, message source advanced by 256 bytes and the
reloaded next public index. Those generic per-record lemmas retain explicit
next-index geometry/content and next-buffer bounds; the loader-derived
boundary projection below discharges the index premise at active ordinals.

`CheckerUnreadMemory` now tracks the two intervals before the first message
and at/after the current message, excluding the low workspace. The reference
is the actual decoded cryptographic-entry snapshot: its public index words
are proved equal to the loader's sorted positions, while its reconstructed
raw bytes come from the decoder rather than the loader's original zero memory.
The invariant is initialized at the actual selector reset and is preserved
through every record's memory writes. `CheckerRecordBoundary` tracks the
remaining count, ordinal, pointers and global registers; its active-core
projection derives index access and contents from the invariant, with no
prepared-next-index premise. Initialization is instantiated from decoded input
for all nonempty position sets. The raw-record factory now covers all `LENGTH`
ordinals, not just the 128-position scoring case: accepted-trace refinement
quantifies over every checker input. The actual initial-input cases now
reject or reach word 2396 within `49725 + 2387*n` cycles and zero calls, under
the existing header length bounds.

`checkerRecordPrefix` composes actual lower traces, duplicate checks and record
latches. Its support induction preserves the loader-derived boundary after
every successful prefix, including the final zero-count boundary, and stops
on the actual mismatch branch. `checker_record_prefix_execution` connects this
trace to the delivered instructions with a uniform `3725*k` instruction budget
and carries unused instructions into the continuation. At every `k≤n`, it uses
at most `4369*k` cycles and `92*k` calls, with exact cycle accounting of
instructions plus seven per call. From decoded word 2367, all records reach
word 2647 or rejection word 2738, within `2073 + 4369*n` cycles and `92*n`
calls. These are record-loop boundaries, not a complete accept/reject theorem.

The record boundary also tracks every cap-leaf occupancy word against the
processed public groups. `checker_record_lower_mark_memory` preserves these
low words through nonce copying, leaf execution and all sixteen lower hashes;
the actual group stores set the current mark to one and preserve other marks.
Consequently `checker_decoded_cap_ready` derives the complete `CapMarkReady`
boundary from decoded input and the finished record loop: canonical leaf
occupancy, raw/footer cursors, evenness, RAM bounds and footer room. No prepared
occupancy or end-pointer premise remains on this boundary.

`checker_decoded_cap_post` follows the actual cap sweep/DFS to word 2718,
deriving exhausted raw input and the original commitment pointer. Root scanning
now also proves its cycle bound: at most sixteen cycles, no public calls, and a
terminal success/failure result for every continuation fuel. `checkerDecodedRun`
composes the record loop, both rejection routes, cap DFS and root halt from word
2367. Its delivered execution uses at most `2073+4369*n+63047` cycles and
`92*n+255` public calls and never remains unfinished.

For nonempty inputs satisfying the existing header length bounds,
`checker_initial_admitted_limits` lifts this to the actual initial state:
at most `112772+6756*n` cycles and `92*n+255` calls. These bounds fit the
delivered `2^40` checker budget and `2^31` query limit over the full `LENGTH`
domain, not merely 128 requests. Header failures now reject in ten or thirteen
cycles; nonzero proofs for empty position sets reject in eighteen cycles, and
the canonical empty check accepts in twenty-one cycles. `checker_initial_limits`
and `checker_run_limits` remove the header and nonempty premises: every actual
delivered checker run terminates within the same bounds, including the loader's
oversized-proof rejection. The query bound here is the execution's public-call
accounting field. `ChainedCheckerRefinement.checker_observation_accounting`
connects that field to the independent recorded observation counter for any
submission. `checker_observation_resources` therefore proves actual delivered
recorded checks terminate, charge at most `2^40` cycles and make at most `2^31`
public calls, without acceptance or header premises.

The same module now derives typed leaf data at every active record boundary,
not only the first record. `checker_boundary_raw_memory` identifies the actual
decoded record at raw stride 498 using the loader-derived unread invariant.
`checker_record_value_data` and `checker_record_nonce_data` identify the
256-byte public value and copied nonce. `checker_record_typed_leaf_rows`,
`checker_record_typed_leaf_digest` and `checker_record_typed_leaf_path_digest`
give the actual two recorded pinned-permutation rows, their digest and its
238-bit lower-path mask at word 2437. The queried index equals the corresponding
attached sorted position. These results cover arbitrary valid cardinalities;
an active record is derived from the outer boundary's remaining-count balance.
Typed lower/cap hash paths and accepted-trace/security certification remain
pending. No delivered bytes, legacy certificate, claim or `Solution.lean` changed.

The delivered-image honest checker query bound is now the stronger
`92*k + min (8*k) 255`, including empty and malformed inputs. It is propagated
through `checker_cap_finish_limits`, `checker_decoded_limits`,
`checker_initial_limits` and `checker_run_limits` in
`ChainedCheckerRecordFinish.lean`. Its `checker_run_query_budget` theorem proves
`result.oracleCalls ≤ CHECK_BUDGET input.positions.card = 100*k` for every
actual delivered run and every cardinality `k`, not just the scored 128.
`checker_decoded_records_limits` separately bounds every record prefix of length
`j ≤ k` by `92*j` calls. This is a linear `100*k` bound, not a fixed 100,000-call
ceiling.

`ChainedCheckerRefinement.lean` now constructs `RecordedChain` witnesses for
canonical first/continuation compression queries (`canonical_queries_chain`).
`checker_hash_recorded_chain` transports these witnesses and the final masked
value through the actual lower/cap wrapper trace using `checker_hash_content`
and `recordRows`. It retains the wrapper's prepared-input hypotheses; lower/cap
path accumulation and concrete `AcceptedTraceRefines` are not yet instantiated.

`ChainedCheckerPathRefinement.lean` specializes recorded chains to every lower
height and to the first sibling using actual read nodes. It proves ordered
recorded-row concatenation, the actual result copy/restoration, the final
238-bit node frame, and the link from word parity to `pathSeed`. The mask return
uses short abstract instruction-memory lemmas. `checker_first_lower_recorded_path`
now proves the first one-level path with the actual read sibling. It instantiates
an abstract single-step constructor only after opaque native observation
wrappers and separate row/node projection equations have been established.
The row projection also uses an abstract mapped-observation lemma, avoiding
kernel normalization of the native state in a direct projection congruence.
`checker_later_lower_recorded_path` covers each later height, and
`checker_lower_suffix_recorded_path` inductively accumulates any suffix with
positive starting height and end height at most sixteen, using actual read
siblings and ordered row concatenation. This includes the empty suffix.
The first-boundary readiness, node/index equations, and the height-one/count-fifteen
suffix specialization now kernel-check separately over abstract states. The
suffix interface also supports a symbolic count with `count + 1 = 16`.
`checker_lower_sixteen_recorded_path` composes the complete sixteen-level
delivered trace. Its closing proof instantiates an abstract observation-join
lemma rather than rewriting native rows or node projections locally.
`ChainedCheckerCapRefinement.lean` derives the cap wrapper's masked child words
from actual heap buffers, constructs its recorded chain at every cap height,
and gives left/right one-level paths through actual result copying, restoration,
masking and the parent-loop return at word 2704. It links the final parent heap
buffer, not just the hash scratch output, to the recorded chain. The two large
backedge jumps are framed by abstract instruction-memory lemmas. Parent-loop
caller PC, parent range, right-child index and heap-base premises remain explicit.
The same module now frames arbitrary other in-heap words/buffers through both
parent loops (excluding their parent/two children) and unmarked-frontier copies
(excluding their destination). It also provides abstract recorded-path append
for symbolic path lengths, including the empty prefix.
`ChainedCheckerCapPaths.lean` proves subtree heap frames and accumulates the
complete eight-level cap DFS into `RecordedPath`, deriving each wrapper's caller
PC, parent range, right-child index and heap-base premises from the DFS position
invariant. Its observations are irreducible and their row concatenation is
characterized separately. `lower_cap_recorded_path` joins any sixteen-level
lower witness ending at the incoming cap heap value to these eight levels.
Instantiating every record's stored lower witness from the whole delivered
observer, the final commitment comparison and `AcceptedTraceRefines` remain.
`cap_marked_eight_recorded_path` transports the eight levels across the actual
255-parent mark sweep, DFS initialization and root-return test: its boundary is
word 2647 through word 2718. The sweep preserves all cap heap buffers; no
per-wrapper caller, height or prepared child-value premises are exposed there.
`ChainedCheckerRecordRefinement.lean` isolates each record's leaf observation,
first lower state, node equation and complete lower observation. Its abstract
suffix-row transport keeps concrete sixteen-level paths out of the row-inclusion
induction. From the loader-derived record boundary it proves the lower path
starts at the decoded nonce and exact typed public entry's pinned leaf digest;
`group_run_heap_node` identifies accepted insertion/deduplication with that
record's resulting stored cap node. Carrying every earlier stored witness
through the whole outer observer is provided by `ChainedCheckerRecordObserver.lean`.
`record_prefix_stored` preserves every earlier typed lower opening and both pinned
rows through the actual symbolic-count `checkerRecordPrefix` observer. Earlier
cap heap endpoints survive later lower traces and both insertion branches: a
repeated group is already occupied, so its stored value is not overwritten.
`decoded_record_openings` specializes this to all records from the decoded input.
The induction is over an abstract observer; separate opaque result projections
discard instruction/cycle fields before instantiating it on the delivered trace.
`ChainedCheckerAcceptedRefinement.lean` now composes these witnesses with the
actual cap observer: `decoded_index_opening` supplies a complete 24-level opening
and both pinned rows for every requested public index. The root is initially the
actual cap heap node. Separate boundary/mark/DFS frames preserve all 32 submitted
commitment bytes; `cap_observed_root_execution` identifies an accepted root check
with the low 238 bits of that commitment. `cap_finish_observation` carries the cap
rows unchanged through the actual root check and execution charging.
`decoded_observation_openings` transports all evidence through the actual full
decoded checker. Header/decoder rejection and empty-position cases then give
`checker_accepted_trace_refines : AcceptedTraceRefines canonicalEncoding
Artifact.submission`, without prepared-memory or header-admission hypotheses.
`checker_observation_adaptive_budget` transports the actual delivered-image
`checker_run_query_budget` to recorded observations (at most `100*k` at every
`k`); this supplies the replay bound in that concrete refinement.
`delivered_checker_binding` applies the proved adaptive recorded-replay bound to
the actual image-derived scheme and establishes its 120-bit binding property.
`ChainedDeliveredHiding.lean` supplies `delivered_chain_transcript` for the exact
delivered commit/open images. Its builder uses compression alone, the pinned
digest tape and only the salts at opened positions. Valid-domain heap congruence
and typed leaf contents identify the actual serialized root and packet; actual
commit seed sampling and opening execution give the executable transcript law.
`delivered_scheme_hiding` applies the proved adaptive nonce-chain hiding bound,
giving `min 1 ((budget+1)/2^120)` for every opening cardinality and query budget.
`parsed_payload_complete` proves native acceptance of every canonical split
payload, including empty tails and zero padding. `checker_footer_encoded_fits`
and `checker_footer_encoded_accepts` derive the footer guard and acceptance flag
from the actual encoded bytes. `checker_encoded_input_decodes` composes the
delivered loader and decoder through word 2367 within `47652+2387*k` cycles.
`checker_delivered_opening_decodes` specializes this to actual delivered opener
outputs at every nonzero cardinality; `checker_cached_input_raw_records`
identifies the reconstructed records with the exact cached typed records.
`checker_delivered_empty_opening_accepts` proves honest checker acceptance at
cardinality zero, with actual execution taking 21 cycles and no public calls.
`lower_sixteen_recovers_heap` proves the delivered sixteen-level lower trace
recovers the canonical cap-group node from native first-path readiness,
canonical raw record bytes and the matching initial leaf node. The proof covers
both sibling orders, all per-height schedules and arbitrary record bases.
`later_recorded_sibling_data` identifies actual copied sibling bytes through the
two-byte padding stores; `lower_record_raw_frame` preserves the complete input
record through every level. The suffix induction includes the empty suffix.
Opaque first-boundary facts and abstract observation transport keep the final
first-plus-fifteen composition within the unchanged kernel/resource budgets.
`cap_loop_recovers_heap` identifies the actual cap-loop hash with the canonical
parent whenever its two heap children are canonical. `cap_frontier_recovers_heap`
identifies the delivered 30-byte frontier copy and padding with the full 256-bit
canonical heap slot. `cap_finish_buffer` proves the complete 32-byte result of
the delivered cap return's 238-bit mask, rather than only its low-bit projection.
`checker_honest_record_leaf` now instantiates the actual loader-to-leaf contents:
the parsed 121-bit nonce is exactly the delivered salt, and the public entry and
sorted index produce the committed canonical leaf. `checker_honest_path_raw`
carries the complete canonical raw record through the actual nonce/leaf calls
and lower-path setup. `checker_honest_record_lower` composes these facts with all
sixteen levels: for every active record, the actual lower observation produces
the full 256-bit canonical cap-group slot, including its zero high bits.
`lower_sixteen_digest_fits` proves this full-width masking invariant independently
of the heap contents; `cap_loop_recovers_full_heap` likewise upgrades the native
cap-loop result to a full-width slot equality.
`checker_honest_record_step` proves both fresh insertion and full-width duplicate
comparison accept, preserving every marked canonical group slot.
`checker_honest_prefix` carries this invariant through any remaining record
count, including the empty prefix. `checker_honest_all_records` instantiates the
zero-mark loader boundary and proves no record rejects at any nonzero opening
cardinality. Its induction is over an abstract observer; native projections are
instantiated afterwards, avoiding kernel recursion without raising budgets.
`cap_tree_canonical` now proves full-width canonical content for the actual cap
DFS at every height through eight, from canonical selected-group slots and the
actual raw frontier bytes. It covers unmarked frontier reads, marked leaves,
both recursive subtrees and the delivered parent hash, preserving sibling
slots and unread footer bytes. `CapFrontierContents` tracks the ordered 30-byte
frontier fields; its append and native memory-frame lemmas compose recursive
reads without strengthening the machine premises.
`checker_honest_footer_contents` instantiates the actual decoded cached footer
after every record, and the mark-sweep/DFS/root-return composition preserves the
full canonical root. `checker_honest_root_execution` proves that the actual
four-word commitment comparison succeeds. `delivered_scheme_completeness` now
proves honest acceptance for every oracle, message and opening cardinality,
including the empty case, for the scheme derived from the delivered images.
The replacement certificate, arbitrary-trapdoor opener termination, measured claim/Solution
migration and official/VM verification remain unfinished.

### Delivered-byte diagnostic measurements

The manifest SHA-256 is
`b26f86911f0a56a0b0404a1682282b30c66811f2a22ac85e1339b71ffe98bbf3`.
A full instruction-by-instruction RV64 emulator run, with zero message/private
coins, constant-zero compression and the identity permutation, measured the
delivered commit image at **2,353,177,256 cycles**, **1,636,500,908 instructions**,
**102,382,335 public calls** and one private-randomness call. No loops or hashes
were replaced by resource formulas. Public calls cost eight cycles, MUL/DIV/REM
four, and randomness costs `1 + ceil(bytes/8)`, matching `CommitGolf.Riscv`.

The resulting trapdoor was fed to fresh initial states for the delivered opener:

| Positions | Opening cycles | Proof bytes |
| --- | ---: | ---: |
| Empty | 17 | 0 |
| `0, 1, ..., 127` | 361,568 | 61,934 |
| `i*131072`, `0 ≤ i < 128` | 392,335 | 65,440 |
| `i*262144+j`, `0 ≤ i < 64`, `0 ≤ j < 2` | 389,711 | 65,472 |

All four opening runs were independently replayed with the existing Python
delivered-byte interpreter using exactly the same cached slots and salts. Cycle
counts, proof lengths and every proof byte matched. These are concrete runs,
not a proof that the largest sampled opening cost is the global maximum.
Diagnostic source and output are in
`/home/ubuntu/commit-golf-local-logs/measure-delivered.{cpp,py}` and
`delivered-emulator-validated.log`.

`scripts/run.py` does not run an emulator or measure new metrics: it verifies
the submitted numeric certificate and scores those certified claims. The above
diagnostics are therefore **not an official runner result or verified score**;
`claim.json` and `Solution.lean` have not been migrated to these sample values.

### Arbitrary-trapdoor operational primitives

`ChainedFieldsExecution.raw_fields_range_execution` executes field construction
from address bounds alone, without canonical input bytes or padding.
`ChainedTailAccess.tail_traverse_range_execution` similarly executes the complete
descriptor traversal for arbitrary memory, including zero rows, and proves that
its output cursor advances by at most the row count plus one. In particular,
malformed descriptor bytes do not invalidate this traversal's termination bound.
`ChainedRecordFrame.record_pack_range_execution` composes both operations for
arbitrary record memory. It consumes 498 source bytes and emits at most 497
bytes, even when the source padding/high bytes are noncanonical.
`ChainedRecordIteration.record_iteration_range_execution` adds the actual reset,
decrement and back/exit edge, and
`ChainedRecordLoop.record_loop_range_execution` handles the complete public
record count, including zero, reaching standalone PC 12380. The existing
`record_loop_bound` gives at most 2273 cycles per record for this same run.
`ChainedFooterReady.FooterRangeReady` removes all canonical-byte premises from
the footer invariant. Its emission rule preserves the complete mark table.
`ChainedFooterSubtree.footer_subtree_range_execution` proves the complete
content-free DFS: actual standalone PC 12408 to 12940, advancing source/output/
metadata by 30/29/2 bytes per frontier node and retaining the public marks.
`ChainedRecordMarks.record_loop_range_mark_frame` preserves the complete mark
table through the arbitrary-memory record loop.
`ChainedFooterComplete.footer_complete_range_execution` composes DFS with the
root return, descriptor traversal and halt, within 66448 + 13 times the frontier
length cycles. `ChainedPacketPacking.native_packet_range_execution` composes the
record loop, footer initialization and this footer run.
`ChainedOpeningDelivered.artifact_arbitrary_opening_run` composes the arbitrary
trapdoor prefix, entry, postpass and relocation on the exact delivered image;
`artifact_opening_terminates` proves successful native termination for every
trapdoor and every opening cardinality. The full-domain fuel bound remains the
same as the honest run. No canonical trapdoor bytes are assumed by this theorem.
`ChainedDeliveredHiding.delivered_certificate` assembles admission, actual
machine success and termination, honest completeness and budgets, proof size,
prover cycles, adaptive binding and 120-bit hiding for the exact delivered image.
The proved scored limits are 2353177256 commit cycles, 444579 opening cycles and
65472 proof bytes. `Solution.lean` uses this chained certificate directly.
