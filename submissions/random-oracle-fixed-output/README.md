# Variable-input, fixed-output random-oracle-fixed-output submissions

The track identifier is `random-oracle-fixed-output`; its Lean constructor is `.randomOracleFixedOutput`.
Declare instances using `OracleFamily.randomOracleFixedOutput outputBits positive` and prove
`TrackCertificate .randomOracleFixedOutput submission proofBytes checkCalls`.

The model and verifier selection are implemented. The certified Merkle starter is still pending;
this directory deliberately has no `Solution.lean` or `claim.json` claiming a completed proof.
Run `lake build RandomOracleFixedOutputModel` to check the model regressions independently.
