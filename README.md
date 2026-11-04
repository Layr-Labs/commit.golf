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

Use `submission/` for `Solution.lean`, `claim.json`, `programs.json`, and optional
`CommitGolfCandidate/` modules. The included [salted Merkle submission](submission/README.md)
provides a complete certificate for the current contract. Run the verifier below to
check the submission against the exact checkout and toolchain being used.
`programs.json` delivers the code bytes and ABI described in the submission README.
The verifier requires a kernel-checked equality between those delivered programs and
the submission named in the certificate, and reports the manifest's SHA-256 digest.
It generates `CommitGolf.Artifact` inside its isolated build project before compiling
the submission. The contract/test build below checks the trusted definitions and
regressions; `scripts/run.py` checks the submitted certificate and artifact equality.

```sh
lake exe cache get
lake build CommitGolf CommitGolfTests
python3 -m unittest discover -s verifier/tests
# Supported Linux host with Landlock and user systemd 257 or newer:
bash scripts/setup.sh
python3 scripts/run.py
```

Keep the checkout and verifier work directory outside `/tmp` and `/var/tmp`:
the sandbox's `PrivateTmp` setting hides those host directories. The verifier
uses a fresh directory under the current directory's `.work/` by default.

The runner and Benchmark workflow verify `submission/` directly. There is no oracle
selector: both primitives are available together to every solver.
The score report is written to `scripts/score.json`.

The binding game follows the original sampled-function design: sample the two
primitives once, run the adversary, and check both openings against those same
functions. There is no separate finite/infinite binding game or compatibility layer.

## Preserved baseline code

`CommitGolfBaseline/` and `CommitGolfBaseline.lean` preserve the earlier unsalted Merkle
baseline. These historical sources are excluded from the Lake build, verifier inputs,
and permitted submission imports; they target the superseded contract. The current
salted Merkle implementation and its proofs live under `submission/`.

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
These fixed-parameter bounds measure the specified interpreter's abstract costs;
they do not claim elapsed time on a physical processor.

## Yukon setup

`benchmark.json` defines one standalone, lower-is-better benchmark. Only `submission/`
is editable. On the supported Linux verifier host, `yukon setup` runs `scripts/setup.sh`
and `yukon run` runs `scripts/run.py`; successful verification writes `scripts/score.json`.
The dispatched `benchmark.yml` runs the same setup and scoring inside the verifier VM
and uploads that exact path inside its score artifact.

`Test PR` calls the same benchmark job on the PR's exact head commit. It skips Yukon's
`submissions/*` branches, which Yukon dispatches separately. A failed certificate
check produces no score.

Before import, install the Yukon GitHub App on the repository and confirm Blacksmith
runner access. The workflow must be available on the default branch for dispatch.
Create the `yukon-unsafe` label for contract changes that invalidate pending scores, then
coordinate the benchmark import with the Yukon team. Repository/app administration and
import are separate from these local files. Yukon owns solver submission PRs and promotion;
do not merge those PRs manually.

Solvers should record reproducible results and provenance in submission notes. Use GitHub
Discussions for partial research when enabled, and remove secrets and private data before
posting either notes or discussions.

## License

See `LICENSE` and `THIRD_PARTY_NOTICES.md`.
