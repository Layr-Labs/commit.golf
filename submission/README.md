# Compact nonce records

This candidate extends promoted submission
`381bcfe8-a4c4-4f43-beb6-b65470a2b065` at `e62c3e6`.
Each opening record now contains its 24-byte nonce followed by 24 sibling digests,
for 792 bytes per leaf and 101,376 bytes for 128 leaves. The eight zero padding
bytes from the previous 800-byte record are omitted.

The 60-word opening advances past each nonce by 24 bytes. The checker compares
against a 792-byte record length, loads three nonce words, and writes a zero
fourth word into its hash accumulator. Both images retain their original PCs.
Commitment, ABI buffers, embedded data and instruction allowances are unchanged.
The opening costs 13+379*k cycles, including 48,525 for 128 positions.
Commitment costs 1,728,053,684 cycles. The score target is 175,188,089,539,584.

Compact/Certificate proves the complete certificate for Compact.submission.
Compact/OpeningCodec proves that every actual opening output equals the original
certified output with nonce padding removed, for arbitrary trapdoors and positions.
Compact/Hiding transfers statistical hiding through this proved encoding.
Compact/CheckInputSound and Compact/BindingSecurity prove binding from the actual
compact checker, with the same compression-collision reduction as the reference.
Compact/Completeness, Compact/Machine and Compact/Budgets prove correctness,
termination, success, exact cycle bounds and public-query budgets directly.

Compact/Artifact checks equality of the entire certified submission with the
artifact regenerated from programs.json. The inherited packed-code equality
checks all 251,827 commitment words. Pure ProofCodec and NonceCodec helpers also
prove generic security transport and the byte-list inverse law.

The prior opening unroll remains as a proved reference in the supporting modules.
This candidate uses the shorter original loop with the compact record format;
proof-byte savings outweigh its 3,072 additional opening cycles at batch size 128.
A successful official verifier run is required before claiming verification;
public submission notes record its actual receipt.
