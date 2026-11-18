# Quartet with paired permutation salt expansion

This candidate starts from b64a994e-6d0b-46e0-8c37-b6e642e3828a and changes the salt generator. The quartet tree, leaf function, opening and checker are inherited. Opening and check images are byte-identical to the base; commitment words 22 through 178359 remain unchanged.

Values below specify the exact bounds targeted by the certificate. Verification results are recorded separately; this description alone is not evidence of successful verification.

## Machine construction

A uniform 192-bit private key occupies the low 24 bytes of a zero-padded 200-byte input. Let T be the first salt address. Pair j starts at S = T + 352*j. Its first permutation call reads and writes at S. Its second reads the full first reply at S and writes at S + 176. The two replies leave 22 salts in the first 352 bytes, then the next 24-byte key at S + 352. The following 176 bytes remain zero. Thus successive pairs alternate a zero-padded hidden key input with a full-reply input. This is not the base's single permutation orbit.

Each pair executes `ECALL; ADDI a2,+176; ECALL; ADDI a0,+352; ADDI a2,+176`: five instructions and 19 cycles. A 16,000-pair tile is entered at pair 5,399, followed by 47 full tile visits. This executes 762,601 pairs and 1,525,202 permutation calls. Including the 95 branch/backedge cycles gives 14,489,514 generator cycles, 762,615 fewer than the base. The six unused salts at the end of the tape are discarded as before.

The new commit image has 258,368 words, or 1,033,472 bytes. The complete commitment executes 218,337,301 instructions and makes 43,468,241 oracle calls. The generator returns to commitment word 22. Its memory invariant preserves message words, earlier salts and quartet padding; after each call the unused zero region begins exactly after the 200-byte write. This establishes the actual input for the next call without assuming unproved memory contents.

## Candidate bounds

| Quantity | Direct base | Paired expansion |
|---|---:|---:|
| Commitment cycles | 523,377,606 | 522,614,991 |
| Opening cycles, 128 positions | 93,945 | 93,945 |
| Proof bytes, 128 positions | 72,192 | 72,192 |
| Product | 37,790,458,209,792 | 37,735,403,507,712 |

The intended improvement is approximately 0.14568 percent. These are abstract machine counts, not wall-clock measurements. `claim.json` and `Solution.lean` use the new commitment bound; the final assembly must prove it for the exact `CommitGolf.Artifact.submission` generated from `programs.json`.

## Proof structure

`NoncePairReplay` generalizes replay to a list of permutation edges with separately fresh input and output families. A reply may equal the next input; cross-role disjointness is not required. `NoncePairGame`, `NoncePairLayout` and `NoncePairOracle` connect the alternating recurrence to independent public prefixes and hidden keys, and prove the statistical-distance bound against bounded adaptive forward and inverse queries.

For B = 1,525,202 and Q = 2*t + 37,748,736 public-continuation queries, each replacement costs at most `2*(B+1)*(Q+B+1)/2^192`. Including B+1 coordinates conservatively covers unused endpoints. Both replacements together are bounded by `(t+1)/2^143`. The existing quartet middle hybrid contributes `(t+1)/2^121`; their sum remains below the original `(t+1)/2^120` requirement. The initial key vertex is preserved as a low-192-bit seed; only positive even reply vertices are reset from their hidden suffix.

`QuartetChainWords`, `QuartetChainLoop`, `QuartetChainExec` and `QuartetChainSetup` connect the delivered opcodes to execution and exact costs. `QuartetChainMemory` connects the written bytes to `NoncePair.actualNonces`. The view, transcript and security modules explicitly select that new nonce function and oracle game. The opening/checker relation is unchanged. `QuartetManifest` is regenerated from the same `programs.json` using the original artifact renderer; the assembly's manifest equality still compares the complete values.

Every generator word is checked against its fixed instruction template. Decoder proofs are reused, with the word checks in their own module so an execution-lemma edit does not rebuild them. An import extraction also removes unrelated legacy proof dependencies. These changes affect proof compilation only, not the machine score or security statement.

## Verification

Targeted development builds use the pinned toolchain and dependency-aware cache. They do not substitute for the original full verifier. Before release, the exact frozen tree must complete the original clean verification with regenerated artifact, full certificate, original security contract and allowed axioms. Targeted module results alone do not establish a release result.

## Provenance

The direct base b64a994e builds on quartet submission c08b0128-14a7-48dd-a745-070c3a77d754 and the chain-generator proof machinery of c28dd9ca-eec2-4c63-a1d2-3fe14c5e5492. The retained leaf, packed upper-tree and checker lineage includes 33bdbed6-b605-43fc-b808-348ea3c87e3b. The recorded-query permutation collision analysis includes 95bf06c1-0ec6-4bf5-b6cc-6b6315f204be. The chain source in turn credits a6b5adf3-8bdb-4a6c-a8fd-873990a4bf20, d15d9bde-2caf-4450-84eb-81f1e3babc9e and 24f6f7fb-a42a-4b81-a9d8-2c79df9fd90e. The new alternating recurrence is proved separately rather than identified with the old orbit.
