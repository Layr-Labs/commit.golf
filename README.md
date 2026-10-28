# commit.golf

Design a hiding vector commitment scheme using two independent ideal primitives:

- One **512→256-bit compression function**.
- One **1,600→1,600-bit permutation**, supporting forward and inverse queries.

Both are available together through the fixed `PublicSpec` interface. Solvers can implement
compound functions from these primitives. Every underlying primitive call counts,
including repeated and inverse queries. Submissions cannot declare extra instances,
change widths, or access a built-in variable-input RO or XOF.

## Current consolidation stage

Submissions require `Certificate`:
completeness, binding, statistical hiding, honest budgets, and resource bounds.
See [RULES.md](RULES.md) for the current contract.

This change consolidates oracle selection only. The agreed 120-bit security,
2,048-bit leaves, 128-element scored opening, and combined RISC-V-cycle × size
score are subsequent changes. The current code still uses the earlier parameters
and `(proofBytes, checkCalls)` metrics. No cycle certification is claimed here.
The consolidated branch currently contains the noninteractive scheme interface;
interactive work is not yet incorporated.

## Submit and validate

**`submission/` is the only solver-editable directory.** All supporting implementation
and proof modules must live inside it. The contract, parameters, oracle definitions,
verifier, build configuration, scripts, and workflows are maintained by the challenge
authors and are not part of a submission.

Use `submission/` for `Solution.lean`, `claim.json`, and optional
`CommitGolfCandidate/` modules. There is no certified starter for this target yet.

```sh
lake exe cache get
lake build CommitGolf CommitGolfTests
python3 -m unittest discover -s verifier/tests
# Supported Linux host with Landlock and user systemd:
bash scripts/setup.sh
python3 scripts/run.py
```

The runner and Benchmark workflow verify `submission/` directly. There is no oracle
selector: both primitives are available together to every solver.
The score report is written to `scripts/score.json`.

The binding game follows the original sampled-function design: sample the two
primitives once, run the adversary, and check both openings against those same
functions. There is no separate finite/infinite binding game or compatibility layer.

## Preserved baseline code

`CommitGolfBaseline/` and `CommitGolfBaseline.lean` preserve the old implementations,
proofs, and baseline tests for later adaptation. They are excluded from the Lake
build, verifier inputs, and permitted submission imports. They do not currently
compile against the simplified oracle interface.

All active oracle definitions are in `CommitGolf/Oracle.lean`. The configurable
family, RO/XOF implementations, lazy-state machinery, and `CommitGolf/Oracle/`
directory have been removed. Oracle regression tests live in `CommitGolfTests.lean`.

## License

See `LICENSE` and `THIRD_PARTY_NOTICES.md`.

Oracle-query counts are not cycle costs: each primitive call still counts as one query.
The planned cycle score must account for the concrete implementation cost of both primitives,
including the wider permutation; no measured cycle costs are enforced yet.
