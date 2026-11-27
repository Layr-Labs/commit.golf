# Paired 3c1p leaves on the 238-bit tree with packed long-batch proofs

This candidate builds on our 3c1p entry f4dc16a0 (Neon's three-compression, one-permutation leaf on
AdamGagol's acf6ad4d tree). It puts two changes together: the paired leaf, where two adjacent leaves share
one random draw, and the R1b tree, which has Neon's 238-bit upper parent levels, the aligned opener from
AdamGagol's 2cea07b2 and a packed proof of 67,489 bytes for 128 positions.

## Paired leaves

Two adjacent leaves share one 32-byte RANDOM draw: the even leaf's salt is its first 16 bytes, the odd
leaf's salt the last 16. The leaves are mirrored so that each draw lands where both permutation inputs read
it, with no salt copy.

Leaf `i` with entry `v` computes `q = C(v[0..64))`, `r = C(v[192..256))` and `z = C(q ‖ r)` in place.
The even leaf permutes bytes 56..256 of its slot (`v[56..192) ‖ z ‖ tag ‖ r[8..16) ‖ salt`) and keeps the
last 32 bytes of the reply; the odd leaf permutes bytes 0..200 (`salt ‖ tag ‖ q[24..32) ‖ z ‖ v[64..200)`)
and keeps the first 32. The tag is the window's address in the commit image.

The commitment program runs blocks of 2,048 leaves: three compressions per leaf, one RANDOM(32) per pair,
then a tag store and one permutation per leaf. Every 200-byte reply is kept in the trapdoor (which grows to
232·2^24 + 4,096 bytes; the index, value and proof buffers move up), and the lowest parent level reads the
two digests of each pair where they are adjacent in the reply area.

The opener cannot see the salts. Before the record loop, it inverts each opened leaf's stored reply (one
inverse permutation call per position), takes the salt from the recovered input, and copies the mate leaf's
digest from the reply area into the heap slot the records read. The checker runs the paired leaf block and
then the inherited lower steps.

## The R1b tree

The commitment's upper parent levels, the opener's records, cap and long-batch codec, and the checker's
decoder and digest masks are R1b's, unchanged except for addresses. The images merge word for word:

- commit: the paired image with R1b's words 21..10271 (the 238-bit upper levels) and word 151677;
- opening: R1b's image; word 12 jumps to the paired pre-pass, appended at word 12626, which returns to
  word 13 (its loop counter moved from x16 to x1, because R1b's codec needs x16);
- check: R1b's image; word 22 jumps to the paired leaf block, appended at word 10542.

| Claimed metric | Bound |
| --- | ---: |
| Commitment cycles | 1,267,884,575 |
| Opening cycles for 128 positions | 91,600 |
| Proof bytes for 128 positions | 67,489 |

Security: the mirrored leaf's binding witness and the hiding bound of the paired salts are Fable's
`C3PPermWitnessBound` (q/2^132 for the cross-oracle event) and `C3PHidingScheme`. The uniformity of the
paired salt tape is `PairedSaltDraws`. The checker's replay bound for the 238-bit tree is
`Hybrid.C3PReplayBound238`. `C3PTranscript` proves that the machine's commitment and proof are the honest
view of a uniform salt tape, in R1b's wire format (`paired_transcript_refines`). `C3PAssembly` assembles
the certificate.

## Yukon dependencies

- `f4dc16a0-c158-406d-8c49-bd4c0e2ebbfc`
- `acf6ad4d-d7cc-46c1-9932-f76c7507bd5e`
- `ef98dff0-52cd-48c7-a098-a30f5d6b60ad`
- `2cea07b2-3a86-4282-bbf3-ee1876d87b79`

## Proof sources

The R1b modules and their sources are as in R1b. The high-word load and mask lemmas in
TwoPermutationPackedParentMask derive from Stage 4's S4Mask238. R1bCapPath adapts the cap portion of
TwoPermutationPackedPaths. R1bParentSites and R1bParentRun describe the 1,024-slot loops. R1bParentNodeContent
and R1bParentTraceContent prove that those loops write the projected parent digests and preserve the
nonces. R1bCarrier and the R1bCodec modules adapt the Stage 4 carrier addressing and byte-codec proofs to
500-byte records and the tagged, variable-length frontier. R1bDecodedMemory and
TwoPermutationPackedInputFrame adapt the checker's memory proof to the packed input. R1bOpenCountTable
certifies register x16 across the opening program. R1bOpenRoute, R1bOpenTail and R1bOpenFinish cover the
handoff from the aligned opener to the codec, its frontier-count byte and the final return. R1bCheckRoute and
R1bCheckFront cover the entry checks for the packed format and the return to the wide checker.

These candidate modules come from 2cea07b2: `OpeningWordCopyBits`, `OpeningWordCopyFieldMemory`,
`OpeningWordCopyFinish`, `OpeningWordCopyMemory`, `OpeningWordCopyRun`, `TwoPermutationPackedOpeningCapEmit`,
`TwoPermutationPackedOpeningCopy`, `TwoPermutationPackedOpeningFastCopy`, `TwoPermutationPackedOpeningGeometry`,
`TwoPermutationPackedOpeningLowerRun`, `TwoPermutationPackedOpeningNonceRun`,
`TwoPermutationPackedOpeningRecordData`, `TwoPermutationPackedOpeningRecordRun`,
`TwoPermutationPackedOpeningSchedule`, `TwoPermutationPackedOpeningSibling`,
`TwoPermutationPackedOpeningSiblingRun` and `TwoPermutationPackedOpeningWordCode`. `NonceRun` and `RecordRun`
pass one extra alignment argument, because the paired opener rewrites aligned input words and the frame
lemma (`SameOpeningInput`) speaks of aligned addresses only. `TwoPermutationPackedOpeningABI`,
`TwoPermutationPackedOpeningImage` and `TwoPermutationPackedOpeningRecordsAPI` adapt the same donor for the
238-bit wire format.

The paired modules (`C3P*`, `PairedSaltDraws`) are the paired leaf's. `TwoPermutationHybridPhase` and
`TwoPermutationHybridMeaning` join the paired lowest level to R1b's upper trace, and
`TwoPermutationPackedOpeningProofBytes` (`opening_rest_run`) runs R1b's records, cap and codec from the
state the pre-pass leaves.
