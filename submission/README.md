# Fall directly into the opening path

This candidate extends promoted submission `6a5236e3-adfa-4380-b441-3b0a9cd846d1`
at `763eb9c`. Commitment, checker, ABI, compact proof format and the zero-counter
invariant are retained.

The per-position prefix previously jumped from 4232 to 4248 over padding. The
new 353-word image removes that jump and three unused words, placing the path
at 4232 directly after the salt-address calculation. The fourteen-cycle prefix
falls through into twenty-four thirteen-instruction bodies. The three-cycle
outer latch begins at 5480, the return block at 5492 and the final PC at 5504.
Both relocated branch encodings are checked against the delivered words.

Compact/NoJumpPrefix proves the shorter prefix and relates it to the reference
state with its PC set to 4232. NoJumpLoop and NoJumpBounds check the relocated
path and transfer its memory bounds. NoJumpPosition and NoJumpPositions prove
329 cycles per position while carrying the counter-zero invariant. NoJumpInput
proves execution from every actual ABI input, including arbitrary trapdoors and
empty position sets. NoJumpEquivalence proves equality of the machine-derived
scheme with the certified compact reference. NoJumpCertificate transfers security
through that equality and proves actual success, termination and resources.
NoJumpArtifact proves equality of the entire delivered submission with the
independently regenerated artifact, retaining the full packed commitment proof.

Proof size is 101,376 bytes. Commitment costs 1,728,053,684 cycles. Opening 128
leaves costs 13+329*128 = 42,125 cycles. The target score is
175,187,440,733,184, improving the promoted frontier by 12,976,128.
The public submission note records the official verifier receipt.
