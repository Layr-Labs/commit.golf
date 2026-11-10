# Submission

This is the sole solver-editable directory. Put `Solution.lean`, `claim.json`, `programs.json`, and
optional supporting Lean modules under `CommitGolfCandidate/` here.

Define `CommitGolf.Challenge.submission : CommitGolf.Submission` with three RISC-V
images (commit, opening, check), buffer sizes/addresses, and instruction allowances.
The scheme used in security games is derived from these images. Prove:

```lean
CommitGolf.Challenge.certificate :
  CommitGolf.Certificate submission proofBytes commitCycles openingCycles

CommitGolf.Challenge.submission_matches_artifact :
  submission = CommitGolf.Artifact.submission
```

`claim.json` must contain exactly `proofBytes`, `commitCycles`, and `openingCycles`.
These are certified worst-case honest bounds for 128-position openings. The score
is `(commitCycles + openingCycles) * proofBytes`, including one full commitment.
The certificate also requires hiding, binding, completeness, query budgets, successful
honest machine execution, valid image layouts, and termination on all inputs.

Both fixed oracles are available together: 512→256 compression and 1,600-bit permutation
with its inverse. Each call costs one public query and eight abstract machine cycles.
Private coins are allowed for commitment and opening, but not checking. See
[RULES.md](../RULES.md) for the byte layout, syscall interface, and complete requirements.

Run `bash scripts/setup.sh` and `python3 scripts/run.py` on the supported Linux
verifier host. Historical baselines remain separate and uncompiled.

## Delivered programs

`programs.json` contains exactly these fields:

- `schemaVersion`: the integer `1`.
- `sizes`: integer byte capacities `trapdoor` and `proof`.
- `layout`: integer byte addresses `message`, `commitment`, `trapdoor`, `indices`, `values`, and `proof`.
- `steps`: positive instruction allowances `commit`, `opening`, and `check`.
- `images`: `commit`, `opening`, and `check`, each containing `code` and `data` strings.

Both strings use lowercase hexadecimal bytes, with no prefix or whitespace. `code`
contains complete 32-bit instructions in little-endian byte order: the instruction
`0x00000073` is encoded as `"73000000"`. `data` contains the embedded bytes in increasing
address order. An empty byte string is `""`. Each image's combined code and data must
be smaller than 1 MiB. Capacities and addresses are at most `2^36`; instruction
allowances are at most `2^48`. The certificate additionally enforces the layout and
machine requirements in `RULES.md`.

Unknown or duplicate fields, noninteger metadata, noncanonical hexadecimal, and
truncated instructions are rejected before compilation. The manifest is at most 8 MiB
and counts toward the submission's existing 32-MiB limit.

The verifier freezes this file, generates a concrete `CommitGolf.Artifact.submission`
from the delivered bytes and ABI, and requires the equality theorem above in addition
to the security certificate. It generates that module inside its isolated build project.
Import `CommitGolf.Artifact` in `Solution.lean`; do not provide that module yourself.
The generated module packs bounded little-endian chunks, with exact counts, into balanced
named trees. Its pure Lean decoder yields the same image lists; this internal encoding
does not change the delivered manifest or image-size limits.

For large images, define the certified submission directly from the generated value:

```lean
import CommitGolf.Artifact

namespace CommitGolf.Challenge

def submission : CommitGolf.Submission := CommitGolf.Artifact.submission

theorem submission_matches_artifact : submission = CommitGolf.Artifact.submission := by
  rfl

end CommitGolf.Challenge
```

The full `certificate` theorem is still required. Build the correctness and security proofs
around this value, using symbolic image properties and the decoder's length/index lemmas
where useful. Maximum-size admission tests use this alias; they do not establish practical
equality checking against an independently constructed large image. In an independent review,
`decide +kernel` comparing the same maximum-size code packed in different chunks had not
finished after 20 minutes. Other proof strategies may work; avoid relying on whole-image
normalization when designing a large submission.

To generate the same module for local proof development, run from the repository root:

```sh
python3 scripts/generate_artifact.py
lake build CommitGolf.Artifact
# After changing submission/programs.json:
python3 scripts/generate_artifact.py --refresh
```

The command uses the verifier's manifest parser and renderer and writes the ignored local
`CommitGolf/Artifact.lean`. Creating or refreshing it clears its compiled artifacts;
when content and permissions are already current, it is left in place. Rebuild after refreshing.
A standalone file importing that module can then be checked with `lake env lean path/to/file.lean`;
this does not stage the supporting modules under `submission/CommitGolfCandidate/` as a Lake
library. Do not include the generated module in your submission. Official verification
regenerates it from the frozen manifest and checks the full certificate and equality again;
local generation or compilation does not certify a submission.

Classical reasoning in proofs is permitted. The manifest supplies the executable
even if the proof chooses its equal value noncomputably.
The accepted score report includes `artifactDigest`, the SHA-256 of the exact manifest
bytes, including JSON formatting. Re-run verification after changing either the
manifest or its equality proof.

## Resource proofs for this implementation

[Resources](CommitGolfCandidate/Resources.lean) applies the upstream stage-composition design to
the included salted Merkle candidate's eight-block leaf. VCVio composes query bounds through intermediate
results and transfers them to the public oracle; ArkLib supplies the immutable entry
source, and CompPoly stores its eight blocks without discarding zero padding. The
candidate [bridge](CommitGolfCandidate/LeafResourceBridge.lean) connects this exact query
program to the hiding proof's leaf budget. These helpers belong to this submission;
other submissions may use different constructions and the certificate fields are unchanged.

These are concrete worst-case operation counts. Source/view construction, encoding and
other pure work are outside that profile. Separate instruction proofs establish machine
cycles, including the checker leaf segment's 194 cycles and eight public calls under its
memory and entry conditions. That segment excludes caller preparation and the continuation;
the full certificate still checks the complete programs' bounds. ArkLib's extractor-specific
typed paths are available at the pinned revisions; an extraction security contract and
its efficiency proof remain separate work. The stored-product helper and isolated machine
segment are compiled supporting lemmas; their imports do not establish separate kernel-replay
evidence. [ResourceTests](CommitGolfCandidate/ResourceTests.lean), imported by `Solution.lean`,
checks that seven calls do not suffice and that block order and trailing zero blocks are preserved.

## Initial implementation

This directory contains the initial machine submission and a complete Lean
`CommitGolf.Challenge.certificate` theorem, including binding and hiding for the
actual machine-derived scheme. The current claims are 102400 proof bytes,
3372220452 commitment cycles, and 48670 opening cycles, giving a score of
**345,320,358,092,800**. The commitment setup retains the baseline's generic constant loads.
The commitment leaf subroutine initializes its five fixed syscall arguments once
per leaf and preserves them across all eight blocks, saving another 35 cycles per leaf.
The checker retains its original independent subroutine. Run the verifier below
before treating a changed claim as accepted.

On 2026-10-28, the Linux verifier accepted the original complete certificate
after an isolated rebuild and Lean kernel replay. That historical claim used
17179869184 commitment cycles and 1048576 opening cycles, scoring
**1,759,325,978,624,000**. It does not verify the tightened claim or a later checkout.

The construction uses a binary Merkle tree. Each 2048-bit leaf is compressed in eight
256-bit blocks starting from an independent private 256-bit salt. A proof contains one
salt and 24 sibling digests for each opened position: 800 bytes per position, or 102400
bytes for 128 positions. The private trapdoor stores the tree and all salts. The
implementation uses compression only; access to the permutation remains available.

- `CommitGolfCandidate/Programs.lean`: instruction assembly, three machine images, layout.
- `CommitGolfCandidate/Model.lean`: reference computation and proved path reconstruction.
- `CommitGolfCandidate/Binding.lean`: proved collision extraction from conflicting salted-leaf openings, with exact query-trace lengths; `BindingSecurity.lean` completes the probabilistic reduction.
- `CommitGolfCandidate/Execution.lean`: proved fuel-splitting equivalence, invariance under extra fuel after halting, a public-query count bounded by instruction fuel, and an eight-cycles-per-step bound for coin-free execution. The last two bounds also apply through the real submission ABI; they do not prove termination. This module also proves that oracle reply writes preserve registers and memory outside the written words.
- `CommitGolfCandidate/Opening.lean`: interpreter proofs checked against the submitted instruction bytes, including memory safety and preservation of unread indices. Setup takes 20 cycles, each position (salt plus 24 siblings) takes 380 cycles, and the successful return costs 10 cycles. The complete position loop is proved under explicit input-buffer invariants.
- `CommitGolfCandidate/OpeningInput.lean`: proves that the trusted ABI establishes those invariants, including exact deserialization of sorted indices. For every trapdoor and position set, the actual opening image succeeds in `30 + 380 * positions.card` cycles, makes zero queries, and returns exactly `800 * positions.card` bytes. The scored batch therefore uses 48670 cycles and 102400 bytes. This module proves the certificate's full `ProofSize 102400` field and opening-specific termination. The complete three-program termination field is proved in `Machine.lean`; cryptographic security remains separate.
- `CommitGolfCandidate/Check.lean`: proves the actual checker rejects malformed lengths (including ABI overflow rejection), accepts empty openings, and compares each reconstructed-root word with the supplied root. In-capacity wrong lengths cost 16 cycles; empty acceptance costs 20; four matching root words cost 12. All these paths make zero oracle queries. The length and empty-opening results are connected to the security-game scheme, and any accepted proof must have exactly `800 * positions.card` bytes. The compression blocks are proved to cost 13 cycles and one query, with exact little-endian digest writeback and preservation of memory outside the output scratch words. The full eight-block leaf-hash subroutine is proved to return in 138 instructions, 194 cycles, and eight queries for every oracle reply sequence, under its entry-point, link, scratch, and input-access invariants. Its source pointer advances 256 bytes and the path/proof metadata is preserved. `LeafRefinement.lean` now connects that loop to the mathematical leaf hash; authentication-path execution is in `CheckPath.lean`, and the full checker termination proof is in `CheckInput.lean`.
- `CommitGolfCandidate/CheckPath.lean`: proves both sibling-ordering branches and the complete 24-level authentication-path execution, under its scratch and readable-input invariants. The loop reaches the root comparison, consumes 768 sibling bytes, preserves the outer checker metadata, and makes 24 queries. Its cost is 648–864 cycles plus four setup cycles, with the exact instruction/cycle count determined by the position bits. This is an execution proof; `PathRefinement.lean` now proves the connection to the reference Merkle-path computation under explicit memory-content and position-bit preconditions. The outer checker loop is proved in `CheckLoop.lean`.
- `CommitGolfCandidate/CheckLoop.lean`: joins index loading, salt copying, eight leaf compressions, 24 path compressions, root comparison, and the outer loop. A mismatch in any root word halts with failure. Successful comparisons advance all pointers and preserve buffer safety. Every loop execution terminates under its input invariants, with at most 1100 cycles and 32 public queries per position plus three exit cycles.
- `CommitGolfCandidate/Counting.lean`: proves that coin-free interpreter executions report exactly the number of calls independently accumulated by the security-game oracle runner.
- `CommitGolfCandidate/CheckInput.lean`: discharges the loop invariants for every actual ABI input, including arbitrary commitments, values, positions, and proof bytes. Proves checker termination in the certificate's probability-one form for every fixed oracle. The actual runner uses at most `1100 * positions.card + 20` cycles and `32 * positions.card` public queries; for 128 positions, those bounds are 140820 cycles and 4096 queries. This does not establish acceptance of honest proofs or the cryptographic security properties.
- `CommitGolfCandidate/CommitLeaf.lean` and `Commit.lean`: exact instruction proofs for setup, private salt sampling, leaf hashing, digest copying, and one full leaf iteration (124 instructions, 180 cycles, eight queries).
- `CommitGolfCandidate/CommitLoop.lean`, `CommitParents.lean`, and `CommitTree.lean`: all leaf and internal-node iterations, root output, and successful HALT. After salt/scratch initialization, tree construction takes `134*N + 3` instructions, `197*N - 4` cycles, and `9*N - 1` queries. These are execution proofs for all oracle answers, not tests or a cryptographic refinement proof.
- `CommitGolfCandidate/CommitInput.lean`: establishes every loop, alignment, and buffer-safety invariant from the actual input loader, for arbitrary messages and salt contents.
- `CommitGolfCandidate/CommitRuntime.lean`: connects setup, private randomness, tree construction, and the actual submitted instruction allowance. Every commitment succeeds in exactly 3372220452 cycles and records 150994943 public queries in the interpreter. `CountingCoins.lean` and `Budgets.lean` connect this to the independent security-game query counter, including private randomness.
- `CommitGolfCandidate/Machine.lean`: proves the complete certificate fields `MachineSuccess`, `Termination`, and `ProverCycles 3372220452 48670`, using the real machine-derived scheme and oracle runner. Completeness, binding, and hiding are supplied by their corresponding modules.
- `CommitGolfCandidate/CountingCoins.lean`: extends the independent counter equality to executions with private randomness.
- `CommitGolfCandidate/CheckEvaluation.lean`: connects the deterministic checker evaluator to the counted oracle runner and proves the scheme checks use at most 32 queries per opened leaf.
- `CommitGolfCandidate/Budgets.lean`: proves the complete `HonestBudgets` field: exactly 150994943 commitment queries, zero opening queries, and at most 32 checking queries per opened leaf.
- `CommitGolfCandidate/Memory.lean`: proves the interpreter’s byte reads recover digest words and combine the two compression-input halves in the intended order.
- `CommitGolfCandidate/LeafRefinement.lean`: proves that both actual leaf loops compute `leafDigest`, with source-memory alignment, separation, and contents as explicit preconditions. The input-loader refinement is in `BufferRefinement.lean`; `CommitHeap.lean` connects it to the complete leaf/parent construction.
- `CommitGolfCandidate/PathRefinement.lean`: proves the actual sibling-ordering operations and complete path loop compute `climb`. The loop consumes the specified sibling digests according to the position bits. The constructed heap is covered by `CommitHeap.lean`; `OpeningOutput.lean` and `HonestRecords.lean` connect the actual emitted path bytes to that heap.
- `CommitGolfCandidate/InputMemory.lean`: proves byte-for-byte correctness of the trusted loader and generic serialization/slicing round trips, including the large private trapdoor.
- `CommitGolfCandidate/BufferRefinement.lean`: connects message and opened-value blocks, commitments, proof bytes, and private-state digests to actual input memory. Proves that opening receives the same private-state digests produced by commitment, and checking receives the same proof digests returned by opening.
- `CommitGolfCandidate/HeapModel.lean`: proves that the machine's heap-indexed sibling path reconstructs the root when stored parents equal the compression of their children; also relates heap directions to leaf-index bits.
- `CommitGolfCandidate/CheckRefinement.lean`: proves a complete checker iteration computes the salted leaf digest followed by all 24 siblings, preserves input buffers, and compares the resulting digest against the original supplied root. Connects this to the heap reconstruction theorem under explicit heap/content invariants.
- `CommitGolfCandidate/CheckAcceptance.lean`: proves the full checker accepts exactly when the proof length is correct and every position's root comparison succeeds, through both the actual input ABI and the security-game scheme. `Completeness.lean` now supplies that ABI-level composition with commitment and opening.
- `CommitGolfCandidate/WriteMemory.lean`: proves byte-exact syscall writes and preservation of disjoint buffers.
- `CommitGolfCandidate/CopyRefinement.lean`: proves complete digest contents and preservation for the actual load/store copy sequence.
- `CommitGolfCandidate/CommitRefinement.lean`: proves that a complete commitment leaf iteration loads its salt, hashes the original eight message blocks, stores the resulting digest, and preserves disjoint input/output regions.
- `CommitGolfCandidate/LeafHeap.lean`: lifts that result to every leaf of the actual loop, with explicit non-overlapping input, output, and salt regions.
- `CommitGolfCandidate/ParentRefinement.lean`: proves the actual descending parent loop constructs every internal node correctly and preserves leaf/salt slots. Paths through the resulting heap reconstruct its root.
- `CommitGolfCandidate/CommitHeap.lean`: establishes message and salt contents from the real loader and random syscall, then proves the full leaf/parent construction has the correct salted leaves and consistent parents for every message, random reply, and fixed oracle.
- `CommitGolfCandidate/OpeningRefinement.lean`: proves every sibling record emitted by the actual path loop comes from the original heap, with earlier records preserved by later writes.
- `CommitGolfCandidate/CommitOutput.lean`: proves the returned commitment equals the constructed heap root and that the final copy preserves the tree and salts.
- `CommitGolfCandidate/CommitSemantics.lean`: proves the exact sampled commitment distribution and its root/heap invariant for every supported execution result.
- `CommitGolfCandidate/OpeningRecords.lean`: proves every salt and sibling record in the complete position loop, including preservation by later iterations.
- `CommitGolfCandidate/OpeningOutput.lean`: carries those records through actual trapdoor serialization, the opening input loader, and returned output memory.
- `CommitGolfCandidate/HonestRecords.lean`: proves the actual emitted salt and path reconstruct the actual returned commitment for every selected leaf of every supported commitment execution.
- `CommitGolfCandidate/CheckHonest.lean`: proves the full checker loop accepts correctly encoded records from a consistent heap, including preservation of the remaining inputs between iterations. `Completeness.lean` discharges those preconditions through the actual ABI.
- `CommitGolfCandidate/InputOrder.lean`: proves the opening indices and dependent checker values use the same sorted order, and proves exact checker index deserialization.
- `CommitGolfCandidate/Completeness.lean`: joins the actual commitment distribution, emitted opening records, checker ABI, and whole checker loop. Proves the full `submission.scheme.Completeness` certificate field for every oracle, message, and opening set.
- `CommitGolfCandidate/CheckSound.lean`: proves every record of an accepted checker run reconstructs the supplied root, including adversarial proof bytes.
- `CommitGolfCandidate/CheckInputSound.lean`: carries checker soundness through the actual input ABI and locates a record for any claimed position.
- `CommitGolfCandidate/BindingMachine.lean`: extracts a compression collision from any conflicting claim accepted by both actual machine checks, using just two 32-call records.
- `CommitGolfCandidate/BindingReplay.lean`: implements that replay through the public query interface; proves its exact 64-call overhead and structural bound for arbitrary replies. Record selection depends only on the claim.
- `CommitGolfCandidate/BindingReduction.lean`: bounds the binding-win probability by the replay collision event, handles large budgets, and proves the 64-call overhead fits the 120-bit target under a 256-bit birthday estimate.
- `CommitGolfCandidate/QueryBudget.lean`: enforces public-query budgets while forwarding private coins and proves exact preservation of the original event-based budget probability.
- `CommitGolfCandidate/CompressionROM.lean`: proves an adaptive compression-cache birthday bound with fresh private coins and both directions of any fixed permutation available.
- `CommitGolfCandidate/CompressionSampling.lean`: proves the lazy compression model and the contract's full-table sampling have the same output distribution, for arbitrary adaptive programs and existing caches.
- `CommitGolfCandidate/Properties.lean`: proved image admission and static arithmetic.
- `CommitGolfCandidate/Tests.lean`: small-tree interpreter/reference comparisons and rejection tests.

- `CommitGolfCandidate/BindingProbe.lean`: records actual compression replies, detects the extracted collision in the lazy cache, and bounds the reduction by the adversary budget plus 128 public queries.
- `CommitGolfCandidate/BindingSecurity.lean`: proves the complete `submission.scheme.Binding` requirement for every adversary and positive query budget, using the actual machine checker and the contract's sampled oracles.
- `CommitGolfCandidate/HidingTree.lean`: defines the reference salted heap and proves its uniqueness from leaf contents and parent consistency.
- `CommitGolfCandidate/HidingMachine.lean`: proves that the actual commitment root and every emitted opening byte equal the reference transcript.
- `CommitGolfCandidate/HidingSalts.lean`: proves that the machine's packed random-bit draw is exactly a vector of independent uniform 256-bit salts.
- `CommitGolfCandidate/HidingDistribution.lean`: proves equality between the complete machine hiding-game distributions and the reference games, including both adaptive adversary stages and the shared oracle. The required TV distance is therefore exactly the reference-game distance.
- `CommitGolfCandidate/HidingFreshness.lean`: bounds guesses of fresh salts after an arbitrary randomized first stage, including adaptively chosen prior query sets. The later hiding modules handle queries made after observing the root and opening.
- `CommitGolfCandidate/HidingQueries.lean`: translates the contract's two-stage hiding budget into structural bounds for both adversary stages, retaining the budget consumed during selection.

## Verification

From the repository root, on Linux with Landlock and user systemd 257 or newer:

```sh
bash scripts/setup.sh
python3 scripts/run.py
```

Keep the checkout and verifier work directory outside `/tmp` and `/var/tmp`, which
the sandbox hides. The verifier defaults to a fresh directory under `.work/`.

The runner freezes `submission/`, rebuilds its modules in isolation, checks the
certificate and artifact equality against the trusted challenge, replays the proofs
in Lean's kernel, and writes the accepted score to `scripts/score.json`. It checks the
admitted files and permits only `propext`, `Classical.choice`, and `Quot.sound` in the
checked theorems' axiom dependencies.

For the trusted contract and Python verifier regression tests:

```sh
lake build CommitGolf CommitGolfTests
python3 -m unittest discover -s verifier/tests
```

These commands check trusted definitions and regression tests. They do not compile
`Solution.lean` or establish submission acceptance; the isolated verifier supplies
the generated artifact module and checks both submitted theorems.

The hiding proof covers the complete game. `HidingLeafReplacement.lean`
isolates an unopened leaf while preserving the exact root and proof bytes;
`HidingCoordinate.lean` bounds one message-coordinate change, and
`HidingHybrid.lean` composes that bound across all coordinates. Opened coordinates
are equal in both messages. `HidingGameIntegration.lean` preserves the joint
first-stage challenge/cache distribution and transfers the observer query bound.
`HidingSecurity.lean` proves the accumulated loss meets `HIDING_ERROR`, then
`Solution.lean` assembles all nine fields into the required certificate.

The historical 2026-10-28 accepted run used Ubuntu 26.04 on aarch64, Lean 4.33.1, systemd isolation,
and compiled Landrun. `scripts/setup.sh` and `scripts/run.py` both exited
successfully. The verifier regression suite also passed all 21 tests. The
verified contract commit was `b037ff7cc15b9b8b0b4b9ffc6c4ffac2981e59f6`.
Rerun verification after changing the submission or contract.
