# commit.golf · rules

Design a hiding vector commitment scheme using the fixed oracle pair below, following
Chapter 18 of [CY24](https://github.com/hash-based-snargs-book/hash-based-snargs-book).
Minimize the certified score for **one full commitment and one opening of 128 leaves**:

`(commitCycles + openingCycles) × proofBytes`

The cycle bounds and opening-proof byte bound are worst-case honest-run bounds, not
sample averages. Commitment bytes, private trapdoor storage, opened values, indices,
and verification cycles are not included in this score.
There is no amortization of commitment cost across multiple openings.

## Parameters and oracles

See [Parameters](CommitGolf/Parameters.lean) and [Oracle](CommitGolf/Oracle.lean).

| Parameter | Value |
| --- | --- |
| Logical leaf size | 2,048 bits (256 bytes) |
| Vector length | 2^24 leaves |
| Commitment size | 32 bytes |
| Scored opening | 128 distinct positions |
| Binding / hiding security bits | 120 / 120 |
| Compression | 512 → 256 bits |
| Permutation, forward and inverse | 1,600 → 1,600 bits |
| Commit query budget | 100 × vector length |
| Opening / checking query budget | 100 × number of opened positions |

The compression function and permutation are sampled independently and uniformly,
once per experiment, and shared by all parties. Solvers may build compound functions
using them; they cannot add oracle instances or change their widths. Every underlying
public query counts once, including repeats and inverse queries. Private randomness
and local computation do not consume query budget, but do incur machine-cycle costs.

The logical leaf size does not constrain the solver's internal tree shape or arity.
All phases remain noninteractive.

## Submitted programs

[Programs](CommitGolf/Programs.lean) defines a submission as three RV64IM images
(`commit`, `opening`, `check`), buffer capacities and addresses, and an instruction
allowance per program. The scheme used in the games is derived from these images;
a separate abstract algorithm cannot stand in for the scored executable.

Each run starts with fresh zeroed memory, embedded image data, and its inputs:

- `commit` receives the full vector and writes a commitment and a fixed-capacity private trapdoor.
- `opening` receives that trapdoor and a set of positions; it writes a variable-length proof.
- `check` receives the commitment, positions, claimed values, and proof; it accepts or rejects.

Positions are sorted and serialized as little-endian 64-bit indices. Leaves, commitments,
and private state use little-endian byte encoding. The buffers are addressed by `a0`–`a5`
(message, commitment, trapdoor, indices, values, proof); `a6` contains the position count,
and `a7` the proof capacity, or supplied proof length for `check`. Opening returns its
proof length in `a1`. Only serialized trapdoor bytes pass from commit to opening.

Admission requires aligned, nonoverlapping buffers below the embedded image data,
images smaller than 1 MiB, and positive instruction allowances at most `2^48`.
Memory is a functional 64-GiB address space; the full input vector occupies 4 GiB.
Input loading and output decoding are interface operations, not charged instructions.
Every program must finish within its allowance on all inputs, including adversarial
proofs and trapdoors. Faults reject; exhaustion is `unfinished`, never success.
Honest commitment and opening must succeed for all messages and opening sizes.
Oversized proofs reject.

## Machine costs

[Riscv](CommitGolf/Riscv.lean) uses sig.golf's pinned RV64IM model and these abstract prices:

| Operation | Cycles |
| --- | --- |
| Ordinary instruction | 1 |
| Multiplication/division, including remainder and word forms | 4 |
| Compression syscall | 8 |
| Forward or inverse permutation syscall | 8 |
| Private randomness, `n` bytes | 1 + ceil(n / 8) |
| HALT | 1 |

Syscalls have no additional ordinary-instruction charge. These are benchmark model
costs, not elapsed time or measured processor cycles. `t0=0` requests an oracle:
`a0` input address, `a1` exact input byte length, `a2` output address, `a3` primitive
(0 compression, 1 permutation, 2 inverse). `t0=1` halts, accepting when `a0=0`.
`t0=2` writes `a1` random bytes at `a0`; this syscall is forbidden in `check`.

## Certificate

[Statements](CommitGolf/Statements.lean) requires one certificate covering:

1. Valid images, buffers, and instruction allowances.
2. Successful honest machine commitment/opening and termination on all inputs.
3. Perfect completeness of the executable-derived scheme.
4. Honest oracle-query budgets for commit, opening, and checking at every opening size.
5. An opening-proof bound of `proofBytes` for all 128-position honest openings.
6. Bounds `commitCycles` and `openingCycles` for those same honest executions.
7. Binding: for every adversary and budget `q ≥ 1`, the probability of conflicting accepted openings while making at most `q` calls is at most `q / 2^120`.
8. Statistical hiding of commitment and opening, as described below.

Honest bounds quantify over every fixed oracle realization, message, and applicable
position set, with probability one over private coins. Binding samples the oracle
pair once and checks both openings using that same pair. Only adversary calls count
in its security budget. Verification retains a query budget and termination requirement,
but its cycles are not part of the score.

## Hiding

[Hiding](CommitGolf/Hiding.lean) compares two experiments. An adversary chooses two
messages agreeing on a shared set of opened positions, plus retained state. One
experiment commits/opens the first message; the other commits/opens the second.
The opened positions are selected before commitment.
The adversary receives the commitment and proof and may query the shared oracle pair.
Its output distributions must have total variation distance at most
`min(1, (t + 1) / 2^120)` for every adversary making at most `t` public queries across
both stages. Every opening size, including zero, is covered. Honest queries do not
consume the adversary's budget. No separate simulator or PPT certificate is required.

## Submit and verify

**Only `submission/` is solver-editable.** Define
`CommitGolf.Challenge.submission : CommitGolf.Submission`, and prove
`CommitGolf.Challenge.certificate : Certificate submission proofBytes commitCycles openingCycles`.
Deliver all image bytes and ABI fields in `programs.json` ([encoding](submission/README.md#delivered-programs)).
The verifier generates `CommitGolf.Artifact.submission` from that file. Also prove
`CommitGolf.Challenge.submission_matches_artifact : submission = CommitGolf.Artifact.submission`;
the generated artifact is fixed, not a comparator definition hole.
Supply exactly those three nonnegative integer bounds in `claim.json`. Optional Lean
modules live under `submission/CommitGolfCandidate/`. The combined score and all reported
numeric metrics must fit within `2^53 - 1`.

The [verifier](verifier/verify.py) runs Lean's comparator on the exact trusted
[certificate template](verifier/Challenge.lean.in), replaying declarations through the
kernel and permitting only `propext`, `Classical.choice`, and `Quot.sound`.
Only accepted certificates produce `scripts/score.json`; failed verification produces no score.
Accepted reports include the SHA-256 digest of the exact delivered manifest.

```sh
lake build CommitGolf CommitGolfTests
python3 -m unittest discover -s verifier/tests
# Official verification requires Linux, Landlock, and user systemd 257 or newer:
bash scripts/setup.sh && python3 scripts/run.py
```

Keep the checkout and verifier work directory outside `/tmp` and `/var/tmp`, which
the sandbox hides. Default work directories are created under the current directory's `.work/`.

Historical baselines remain in `CommitGolfBaseline/`, excluded from builds and submission
imports until adapted. The regression fixtures are not secure submissions.
