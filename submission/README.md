# Single challenge submission

This directory is the sole solver-editable surface. Put supporting Lean modules in
`submission/CommitGolfCandidate/`; do not edit files elsewhere in the repository.

Define `CommitGolf.Challenge.submission : CommitGolf.Scheme`. The scheme uses both fixed primitives automatically. Prove
`CommitGolf.Challenge.certificate : CommitGolf.Certificate submission proofBytes checkCalls`.
The certificate requires hiding and exactly the two fixed primitive instances.

The public oracle interface `PublicSpec` routes `.inl input` to the 512→256 compression function,
`.inr (.inl input)` to the 1,600-bit forward permutation, and `.inr (.inr output)`
to its inverse. In computations with private coins (`world`), wrap these public
queries in one further `.inr`. Every public primitive call costs one query.
Derived functions must be implemented from these primitives, not declared as
additional oracles.

Provide `Solution.lean`, `claim.json` (`proofBytes`, `checkCalls`), and optional
`CommitGolfCandidate/` modules here. Run `python3 scripts/run.py` on the supported
Linux verifier host. There is no certified starter for this target yet.

This is a staged consolidation: binding and hiding target 120 bits and logical leaves are 2,048 bits; batch size and scoring have
not yet been updated to the new meeting decisions. The old baseline library is retained as reference code; its certificates do not
establish eligibility for this challenge.
