# Variable-input, fixed-output random-oracle submissions

The track identifier is `random-oracle`; its Lean constructor is `.randomOracle`.
Declare instances using `OracleFamily.randomOracle outputBits positive` and prove
`TrackCertificate .randomOracle submission proofBytes checkCalls`.

The model and verifier selection are implemented. The certified Merkle starter is still pending;
this directory deliberately has no `Solution.lean` or `claim.json` claiming a completed proof.
Run `lake build RandomOracleModel` to check the model regressions independently.
