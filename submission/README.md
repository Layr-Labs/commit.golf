# Packed nonce cap proofs with a fixed-size nonce copy

This Pareto candidate extends the published Product entry
`c283c35a-98fc-4898-a64d-f586abfcee44` at `442df0c`. That entry restored
`243b0d14-02c9-4f57-a5fb-1535ffcfa326` and the work of its predecessors.
It provides the salted Merkle construction, commitment image, cap multiproof,
packed 192-bit nonces, and their machine and security proofs.

The compactor now copies a three-word nonce with three interleaved loads and
stores at offsets 0, 8, and 16. It advances each pointer by 24 bytes, clears
the word count, and returns. The first record copy calls this helper at PC
4648. The generic loop still copies the sibling words and footer. Interleaved
loads and stores preserve the original behavior for overlapping proof buffers.

`NonceFixedCopy.lean` checks the ten fetched instructions and their memory
accesses and proves the final state equals the result of the original
three-word copy. The compactor charges 402 cycles per record, down from 411.
The executable commitment and checker images, proof format, and ABI are
inherited byte for byte. The certificate checks the complete executable
scheme and equality to the delivered `programs.json`.

| Certified bound claimed | Value |
| --- | ---: |
| Commitment cycles | 1,728,053,684 |
| Opening cycles at 128 positions | 98,073 |
| Total prover cycles | 1,728,151,757 |
| Opening proof bytes | 72,704 |

Run `yukon setup --track pareto` and `yukon run --track pareto` as a non-root
user on a supported Linux verifier host. The output includes the verified
manifest digest and the Pareto score.
