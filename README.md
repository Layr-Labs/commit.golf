# commit.golf

Design a hiding vector commitment scheme using two independent ideal primitives:

- One **512→256-bit compression function**.
- One **1,600→1,600-bit permutation**, supporting forward and inverse queries.

Both are available together through the fixed `PublicSpec` interface. Solvers can implement
compound functions from these primitives. Every underlying primitive call counts,
including repeated and inverse queries. Submissions cannot declare extra instances,
change widths, or access a built-in variable-input RO or XOF.

## Score and certificate

Minimize `(commitCycles + openingCycles) × proofBytes` for one full
commitment and an opening of **128 leaves**. Claims are certified worst-case bounds,
not sample measurements; verification cycles are not scored.

Each submission supplies RISC-V programs for commitment, opening, and checking.
The security-game scheme is derived from those same images. One certificate checks
machine admission, successful honest execution, termination, completeness, query
budgets, proof size, prover cycles, binding, and statistical hiding.

Binding and hiding target 120-bit security, with 2,048-bit logical leaves and 256-bit
commitments. The scheme remains noninteractive. See [RULES.md](RULES.md) for the
machine interface, cost schedule, and security requirements.

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

`CommitGolfBaseline/` and `CommitGolfBaseline.lean` retain the Merkle baseline
unchanged from `master`. These historical sources are excluded from the Lake build,
verifier inputs, and permitted submission imports; they do not compile against the
new contract. A certified submission for the new rules will follow separately.

All active oracle definitions are in `CommitGolf/Oracle.lean`. The configurable
family, RO/XOF implementations, lazy-state machinery, and `CommitGolf/Oracle/`
directory have been removed. Oracle regression tests live in `CommitGolfTests.lean`.

## RISC-V execution

`CommitGolf/Riscv.lean` restores the RV64IM interpreter from this repository's
sig.golf-derived history, using the same pinned `riscv-zkvm` dependency. It handles
the fixed compression and forward/inverse permutation syscalls, private randomness,
and halt/failure, recording abstract cycles and public oracle calls separately.
Ordinary instructions cost one cycle; multiplication and division cost four.
Private randomness retains the historical charge of `1 + ceil(bytes / 8)` cycles.
Compression and forward/inverse permutation syscalls each cost eight cycles, with
no additional instruction charge for the syscall. These prices are fixed in Parameters.

`CommitGolf/Programs.lean` defines input loading, output decoding, the executable-derived
scheme and honest machine runs. The certificate and comparator require cycle bounds
for those runs. The interpreter's memory ceiling is 64 GiB; memory is modeled as a
function, not allocated at that size. A full logical vector occupies 4 GiB.

## License

See `LICENSE` and `THIRD_PARTY_NOTICES.md`.

Oracle-query counts are not cycle costs: each primitive call still counts as one query.
Each public syscall costs eight abstract machine cycles. The certificate enforces
the declared commitment and opening cycle bounds.

### Yukon setup

`benchmark.json` defines one standalone, lower-is-better benchmark. Only `submission/`
is editable. On the supported Linux verifier host, `yukon setup` runs `scripts/setup.sh`
and `yukon run` runs `scripts/run.py`; successful verification writes `scripts/score.json`.
The dispatched `benchmark.yml` runs the same setup and scoring inside the verifier VM
and uploads that exact path inside its score artifact.

`Test PR` calls the same benchmark job on the PR's exact head commit. It skips Yukon's
`submissions/*` branches, which Yukon dispatches separately. Until a complete initial
certificate is present, the benchmark must fail without producing a score.

Before import, install the Yukon GitHub App on the repository and confirm Blacksmith
runner access. The workflow must be available on the default branch for dispatch.
Create the `yukon-unsafe` label for contract changes that invalidate pending scores, then
coordinate the benchmark import with the Yukon team. Repository/app administration and
import are separate from these local files. Yukon owns solver submission PRs and promotion;
do not merge those PRs manually.

Solvers should record reproducible results and provenance in submission notes. Use GitHub
Discussions for partial research when enabled, and remove secrets and private data before
posting either notes or discussions.
