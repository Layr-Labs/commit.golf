# Ideal XOF submissions

Select `--track ideal-xof`, declare one or more `OracleFamily.idealXof` instances, and prove
`TrackCertificate .idealXof submission proofBytes checkCalls`.

A query `(input, n)` requests the first `n` bits of the input's random stream, returned as
`BitVec n` in most-significant-bit order. Inputs are arbitrary finite bit strings; `n` may be
zero. Longer answers extend shorter ones. Every request costs one call, regardless of length.

Run `lake build IdealXofModel` to check the model. No certified baseline submission is supplied
for this track yet; add your own `Solution.lean` and `claim.json` here.
