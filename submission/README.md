# Submission

This is the sole solver-editable directory. Put `Solution.lean`, `claim.json`, and
optional supporting Lean modules under `CommitGolfCandidate/` here.

Define `CommitGolf.Challenge.submission : CommitGolf.Submission` with three RISC-V
images (commit, opening, check), buffer sizes/addresses, and instruction allowances.
The scheme used in security games is derived from these images. Prove:

```lean
CommitGolf.Challenge.certificate :
  CommitGolf.Certificate submission proofBytes commitCycles openingCycles
```

`claim.json` must contain exactly `proofBytes`, `commitCycles`, and `openingCycles`.
These are certified worst-case honest bounds for 128-position openings. The score
is `(commitCycles + openingCycles) * proofBytes`, including one full commitment.
The certificate also requires hiding, binding, completeness, query budgets, successful
honest machine execution, valid image layouts, and termination on all inputs.

Both fixed oracles are available together: 512→256 compression and 1,600-bit permutation
with its inverse. Each call costs one public query and eight abstract machine cycles.
Private coins are allowed for commitment and opening, but not checking. See
[RULES.md](../RULES.md) for the byte layout, syscall interface, and complete requirements.

Run `python3 scripts/run.py` on the supported Linux verifier host. There is no certified
starter for this target yet; the historical baseline code is preserved but uncompiled.
