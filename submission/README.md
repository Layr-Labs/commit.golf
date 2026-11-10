# Unrolled opening paths

This candidate directly extends promoted submission
`07e37678-7cc7-48f5-a62f-4c6265e91a93` at `4fcc9af`.

The opening repeats the fourteen useful path instructions twenty-four times,
omitting each backward path branch. Its counter still decrements from 24 to zero.
The 381-word image preserves all proof bytes and the reference machine state,
with only the final PC relocated to 5616. Empty openings branch to the new return
block at 5604; the outer loop branches from 5600 back to 4176.

FastOpeningCertificate proves the complete certificate for fastSubmission.
FastOpeningInput proves all-input execution at 13+355*k cycles, including 45,453
for 128 positions. FastOpeningEquivalence proves equality of the machine-derived
scheme with the retained reference scheme, transferring its completeness,
query budgets, proof size, binding and statistical hiding. Machine success,
termination and improved cycles are proved directly for the new image.

Commitment remains 1,728,053,684 cycles, proof size remains 102,400 bytes,
and the score target is 176,957,351,628,800. A successful official verifier run
is required for acceptance; public submission notes record the actual receipt.

FastOpeningArtifact checks the full actual submission against the artifact
regenerated from programs.json. The inherited indexed packed-code equality
checks the unchanged 251,827-word commitment image. The checker, ABI, data and
instruction allowances are unchanged. The old submission definition remains
only as the fully proved reference for the new execution equivalence.
