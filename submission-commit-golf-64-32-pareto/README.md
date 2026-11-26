# 3c1p with signed output windows and aligned opening copies

This entry builds on f4dc16a0 (Neon’s three-compression, one-permutation leaf and its binding and hiding proofs) and AdamGagol’s acf6ad4d tree. It uses the signed output-window design from AdamGagol’s ef98dff0 and the aligned opening program from his 2cea07b2. The first output window starts at the original cursor, rebases after 64 leaves and uses signed offsets for the remaining full 128-leaf windows. Each block ends at the original stop address. This saves the two extra setup instructions in the direct port.

The following candidate modules come verbatim from 2cea07b2.

- `OpeningWordCopyBits.lean`
- `OpeningWordCopyFieldMemory.lean`
- `OpeningWordCopyFinish.lean`
- `OpeningWordCopyMemory.lean`
- `OpeningWordCopyRun.lean`
- `TwoPermutationPackedOpeningCapEmit.lean`
- `TwoPermutationPackedOpeningCopy.lean`
- `TwoPermutationPackedOpeningFastCopy.lean`
- `TwoPermutationPackedOpeningGeometry.lean`
- `TwoPermutationPackedOpeningLowerRun.lean`
- `TwoPermutationPackedOpeningNonceRun.lean`
- `TwoPermutationPackedOpeningRecordData.lean`
- `TwoPermutationPackedOpeningRecordRun.lean`
- `TwoPermutationPackedOpeningSchedule.lean`
- `TwoPermutationPackedOpeningSibling.lean`
- `TwoPermutationPackedOpeningSiblingRun.lean`
- `TwoPermutationPackedOpeningWordCode.lean`

The following modules adapt the same donor for the 238-bit wire format.

- `TwoPermutationPackedOpeningABI.lean`
- `TwoPermutationPackedOpeningImage.lean`
- `TwoPermutationPackedOpeningRecordsAPI.lean`

The opening image module starts with the 2cea07b2 literals and adds the long-batch dispatch and codec tail. The opening transcript module adapts the new opening bound to the 3c1p transcript. The C3 commit fetch, pass, block and loop proofs cover the new output addresses and costs. 

This variant adapts Neon’s 238-bit upper tree and packs long 128-record proofs. It reuses Fable’s C3XReplay238 and K3T238 witness, birthday and budget modules. The carrier and RISC-V codec proofs derive from the team’s 96-32 Stage 4 implementation. Its checker expands the encoded proof and applies the matching digest masks.

## Yukon dependencies

- `f4dc16a0-c158-406d-8c49-bd4c0e2ebbfc`
- `acf6ad4d-d7cc-46c1-9932-f76c7507bd5e`
- `ef98dff0-52cd-48c7-a098-a30f5d6b60ad`
- `2cea07b2-3a86-4282-bbf3-ee1876d87b79`
- `98b5b7e9-6874-4546-a830-b8b319896c6c` (the K3T238 witness, birthday and budget modules, byte-identical)

## Proof sources

The high-word load and mask lemmas in TwoPermutationPackedParentMask derive from Stage 4’s S4Mask238. R1bCapPath adapts the cap portion of TwoPermutationPackedPaths. R1bParentSites and R1bParentRun describe the new 1,024-slot loops. R1bParentNodeContent and R1bParentTraceContent prove that those loops write the projected parent digests and preserve the nonces. R1bCarrier and the R1bCodec modules adapt the Stage 4 carrier addressing and byte-codec proofs to 500-byte records and the tagged, variable-length frontier.

R1bDecodedMemory and TwoPermutationPackedInputFrame adapt the checker’s memory proof to the packed input. R1bOpenCountTable certifies register x16 across the delivered opening program. R1bOpenRoute, R1bOpenTail and R1bOpenFinish cover the handoff from the aligned opener to the codec, its frontier-count byte and the final return. R1bCheckRoute and R1bCheckFront cover the entry checks for the packed format and the return to the wide checker.
