# Submission

This is the sole solver-editable directory. Put `Solution.lean`, `claim.json`, and
optional supporting Lean modules under `CommitGolfCandidate/` here.

Define `CommitGolf.Challenge.submission : CommitGolf.Submission` with three RISC-V
images (commit, opening, check), buffer sizes/addresses, and instruction allowances.
The scheme used in security games is derived from these images. Prove:

```lean
CommitGolf.Challenge.certificate :
  CommitGolf.Certificate submission proofBytes commitCycles openingCycles
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

Run `python3 scripts/run.py` on the supported Linux verifier host. There is no certified
starter for this target yet; the historical baseline code is preserved but uncompiled.

## Initial implementation status

This directory now contains a **draft**, not a certified baseline. `Solution.lean`
defines the machine submission but deliberately has no `certificate` theorem. The
numbers in `claim.json` are targets awaiting the complete proof, not an accepted score.
The comparator must reject this state.

The construction uses a binary Merkle tree. Each 2048-bit leaf is compressed in eight
256-bit blocks starting from an independent private 256-bit salt. A proof contains one
salt and 24 sibling digests for each opened position: 800 bytes per position, or 102400
bytes for 128 positions. The private trapdoor stores the tree and all salts. The
implementation uses compression only; access to the permutation remains available.

- `CommitGolfCandidate/Programs.lean`: instruction assembly, three machine images, layout.
- `CommitGolfCandidate/Model.lean`: reference computation and proved path reconstruction.
- `CommitGolfCandidate/Binding.lean`: proved collision extraction from conflicting salted-leaf openings, with exact query-trace lengths; the probabilistic security reduction is still missing.
- `CommitGolfCandidate/Execution.lean`: proved fuel-splitting equivalence, invariance under extra fuel after halting, a public-query count bounded by instruction fuel, and an eight-cycles-per-step bound for coin-free execution. The last two bounds also apply through the real submission ABI; they do not prove termination. This module also proves that oracle reply writes preserve registers and memory outside the written words.
- `CommitGolfCandidate/Opening.lean`: interpreter proofs checked against the submitted instruction bytes, including memory safety and preservation of unread indices. Setup takes 20 cycles, each position (salt plus 24 siblings) takes 380 cycles, and the successful return costs 10 cycles. The complete position loop is proved under explicit input-buffer invariants.
- `CommitGolfCandidate/OpeningInput.lean`: proves that the trusted ABI establishes those invariants, including exact deserialization of sorted indices. For every trapdoor and position set, the actual opening image succeeds in `30 + 380 * positions.card` cycles, makes zero queries, and returns exactly `800 * positions.card` bytes. The scored batch therefore uses 48670 cycles and 102400 bytes. This module proves the certificate's full `ProofSize 102400` field and opening-specific termination. The complete three-program termination field is proved in `Machine.lean`; cryptographic security remains separate.
- `CommitGolfCandidate/Check.lean`: proves the actual checker rejects malformed lengths (including ABI overflow rejection), accepts empty openings, and compares each reconstructed-root word with the supplied root. In-capacity wrong lengths cost 16 cycles; empty acceptance costs 20; four matching root words cost 12. All these paths make zero oracle queries. The length and empty-opening results are connected to the security-game scheme, and any accepted proof must have exactly `800 * positions.card` bytes. The compression blocks are proved to cost 13 cycles and one query, with exact little-endian digest writeback and preservation of memory outside the output scratch words. The full eight-block leaf-hash subroutine is proved to return in 138 instructions, 194 cycles, and eight queries for every oracle reply sequence, under its entry-point, link, scratch, and input-access invariants. Its source pointer advances 256 bytes and the path/proof metadata is preserved. `LeafRefinement.lean` now connects that loop to the mathematical leaf hash; authentication-path execution is in `CheckPath.lean`, and the full checker termination proof is in `CheckInput.lean`.
- `CommitGolfCandidate/CheckPath.lean`: proves both sibling-ordering branches and the complete 24-level authentication-path execution, under its scratch and readable-input invariants. The loop reaches the root comparison, consumes 768 sibling bytes, preserves the outer checker metadata, and makes 24 queries. Its cost is 648–864 cycles plus four setup cycles, with the exact instruction/cycle count determined by the position bits. This is an execution proof; `PathRefinement.lean` now proves the connection to the reference Merkle-path computation under explicit memory-content and position-bit preconditions. The outer checker loop is proved in `CheckLoop.lean`.
- `CommitGolfCandidate/CheckLoop.lean`: joins index loading, salt copying, eight leaf compressions, 24 path compressions, root comparison, and the outer loop. A mismatch in any root word halts with failure. Successful comparisons advance all pointers and preserve buffer safety. Every loop execution terminates under its input invariants, with at most 1100 cycles and 32 public queries per position plus three exit cycles.
- `CommitGolfCandidate/Counting.lean`: proves that coin-free interpreter executions report exactly the number of calls independently accumulated by the security-game oracle runner.
- `CommitGolfCandidate/CheckInput.lean`: discharges the loop invariants for every actual ABI input, including arbitrary commitments, values, positions, and proof bytes. Proves checker termination in the certificate's probability-one form for every fixed oracle. The actual runner uses at most `1100 * positions.card + 20` cycles and `32 * positions.card` public queries; for 128 positions, those bounds are 140820 cycles and 4096 queries. This does not establish acceptance of honest proofs or the cryptographic security properties.
- `CommitGolfCandidate/CommitLeaf.lean` and `Commit.lean`: exact instruction proofs for setup, private salt sampling, leaf hashing, digest copying, and one full leaf iteration (159 instructions, 215 cycles, eight queries).
- `CommitGolfCandidate/CommitLoop.lean`, `CommitParents.lean`, and `CommitTree.lean`: all leaf and internal-node iterations, root output, and successful HALT. After salt/scratch initialization, tree construction takes `169*N + 3` instructions, `232*N - 4` cycles, and `9*N - 1` queries. These are execution proofs for all oracle answers, not tests or a cryptographic refinement proof.
- `CommitGolfCandidate/CommitInput.lean`: establishes every loop, alignment, and buffer-safety invariant from the actual input loader, for arbitrary messages and salt contents.
- `CommitGolfCandidate/CommitRuntime.lean`: connects setup, private randomness, tree construction, and the actual submitted instruction allowance. Every commitment succeeds in exactly 3959423012 cycles and records 150994943 public queries in the interpreter. `CountingCoins.lean` and `Budgets.lean` connect this to the independent security-game query counter, including private randomness.
- `CommitGolfCandidate/Machine.lean`: proves the complete certificate fields `MachineSuccess`, `Termination`, and `ProverCycles 17179869184 1048576`, using the real machine-derived scheme and oracle runner. These are now checked for every required input; they do not yet prove completeness or security.
- `CommitGolfCandidate/CountingCoins.lean`: extends the independent counter equality to executions with private randomness.
- `CommitGolfCandidate/CheckEvaluation.lean`: connects the deterministic checker evaluator to the counted oracle runner and proves the scheme checks use at most 32 queries per opened leaf.
- `CommitGolfCandidate/Budgets.lean`: proves the complete `HonestBudgets` field: exactly 150994943 commitment queries, zero opening queries, and at most 32 checking queries per opened leaf.
- `CommitGolfCandidate/Memory.lean`: proves the interpreter’s byte reads recover digest words and combine the two compression-input halves in the intended order.
- `CommitGolfCandidate/LeafRefinement.lean`: proves that both actual leaf loops compute `leafDigest`, with source-memory alignment, separation, and contents as explicit preconditions. The input-loader refinement is in `BufferRefinement.lean`; full commitment-heap correctness remains.
- `CommitGolfCandidate/PathRefinement.lean`: proves the actual sibling-ordering operations and complete path loop compute `climb`. The loop consumes the specified sibling digests according to the position bits. Connecting those preconditions to the full commitment heap and opening ABI remains.
- `CommitGolfCandidate/InputMemory.lean`: proves byte-for-byte correctness of the trusted loader and generic serialization/slicing round trips, including the large private trapdoor.
- `CommitGolfCandidate/BufferRefinement.lean`: connects message and opened-value blocks, commitments, proof bytes, and private-state digests to actual input memory. Proves that opening receives the same private-state digests produced by commitment, and checking receives the same proof digests returned by opening.
- `CommitGolfCandidate/HeapModel.lean`: proves that the machine's heap-indexed sibling path reconstructs the root when stored parents equal the compression of their children; also relates heap directions to leaf-index bits.
- `CommitGolfCandidate/CheckRefinement.lean`: proves a complete checker iteration computes the salted leaf digest followed by all 24 siblings, preserves input buffers, and compares the resulting digest against the original supplied root. Connects this to the heap reconstruction theorem under explicit heap/content invariants.
- `CommitGolfCandidate/CheckAcceptance.lean`: proves the full checker accepts exactly when the proof length is correct and every position's root comparison succeeds, through both the actual input ABI and the security-game scheme. Establishing that commitment/opening produce matching heap records is still necessary for completeness.
- `CommitGolfCandidate/Properties.lean`: proved image admission and static arithmetic.
- `CommitGolfCandidate/Tests.lean`: small-tree interpreter/reference comparisons and rejection tests.

From the repository root, after building the contract, compile and test the draft with:

```sh
mkdir -p .lake/build/lib/lean/CommitGolfCandidate
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/Programs.olean submission/CommitGolfCandidate/Programs.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/Model.olean submission/CommitGolfCandidate/Model.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/HeapModel.olean submission/CommitGolfCandidate/HeapModel.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/Properties.olean submission/CommitGolfCandidate/Properties.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/Binding.olean submission/CommitGolfCandidate/Binding.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/Execution.olean submission/CommitGolfCandidate/Execution.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/Counting.olean submission/CommitGolfCandidate/Counting.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/Opening.olean submission/CommitGolfCandidate/Opening.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/OpeningInput.olean submission/CommitGolfCandidate/OpeningInput.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/Check.olean submission/CommitGolfCandidate/Check.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/CheckPath.olean submission/CommitGolfCandidate/CheckPath.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/CheckLoop.olean submission/CommitGolfCandidate/CheckLoop.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/CheckInput.olean submission/CommitGolfCandidate/CheckInput.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/CommitLeaf.olean submission/CommitGolfCandidate/CommitLeaf.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/Commit.olean submission/CommitGolfCandidate/Commit.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/CommitLoop.olean submission/CommitGolfCandidate/CommitLoop.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/CommitParents.olean submission/CommitGolfCandidate/CommitParents.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/CommitTree.olean submission/CommitGolfCandidate/CommitTree.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/CommitInput.olean submission/CommitGolfCandidate/CommitInput.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/CommitRuntime.olean submission/CommitGolfCandidate/CommitRuntime.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/Machine.olean submission/CommitGolfCandidate/Machine.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/CountingCoins.olean submission/CommitGolfCandidate/CountingCoins.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/CheckEvaluation.olean submission/CommitGolfCandidate/CheckEvaluation.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/Budgets.olean submission/CommitGolfCandidate/Budgets.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/Memory.olean submission/CommitGolfCandidate/Memory.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/InputMemory.olean submission/CommitGolfCandidate/InputMemory.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/BufferRefinement.olean submission/CommitGolfCandidate/BufferRefinement.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/LeafRefinement.olean submission/CommitGolfCandidate/LeafRefinement.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/PathRefinement.olean submission/CommitGolfCandidate/PathRefinement.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/CheckRefinement.olean submission/CommitGolfCandidate/CheckRefinement.lean
lake env lean -o .lake/build/lib/lean/CommitGolfCandidate/CheckAcceptance.olean submission/CommitGolfCandidate/CheckAcceptance.lean
lake env lean submission/CommitGolfCandidate/Tests.lean
lake env lean submission/Solution.lean
```

Remaining certification work: prove that commitment constructs a consistent heap and
opening copies the corresponding salts/siblings into its proof records; combine those
facts with the loader round trips and checker acceptance theorem to prove completeness.
The probabilistic binding and statistical hiding reductions also remain.
Admission, successful honest machine execution, termination on all inputs, honest query
budgets, the proof-size field, and the declared prover-cycle bounds are proved. The fixed-coin toy-oracle tests
establish none of the statistical security claims. Once the remaining obligations are
proved, assemble the existing contract's `CommitGolf.Certificate`; do not weaken it or
substitute abstract algorithms for the images. No complete verifier acceptance is claimed.
