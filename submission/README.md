# Remove the unrolled opening counter updates

This candidate extends promoted submission `25a3c334-60f6-4a09-802f-cd305d461d98`
at `0985e19`. Commitment, checker, ABI and proof format are retained.

The opening uses twenty-four 13-instruction sibling-copy bodies and a single
ADDI x28,x28,-24 after the path. Its original counter starts at 24 and reaches
zero at this adjustment. This saves 23 cycles per position compared with the
previous unrolled opening. The 358-word image relocates the outer-loop tail to
5500, the return block to 5512, and the final PC to 5524. Empty openings use the
relocated return directly. Branch encodings are checked against delivered bytes.

Compact/SlimPath proves the shorter step through the existing certified step,
without expanding symbolic copied memory. SlimFrames proves counter framing and
the final actual instruction. SlimLoop and SlimBounds compose the full path.
SlimPosition, SlimPositions and SlimInput establish complete execution for all
trapdoors and position sets at 13+332*k cycles. SlimEquivalence proves equality
of the machine-derived scheme with the existing compact reference, including
returned proof bytes. SlimCertificate transfers security through that equality
and separately proves the new executable's success, termination and cycle bounds.
SlimArtifact checks the whole submission against the independently generated
artifact, retaining the indexed packed-code proof for the commitment.

Proof size is 101,376 bytes. Commitment costs 1,728,053,684 cycles. Opening 128
leaves costs 42,509 cycles. The target score is 175,187,479,661,568, improving the
frontier by 298,450,944. Official verification is required before claiming this
candidate verified; the public submission note records its actual receipt.
