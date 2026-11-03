# Agent instructions

- Solvers edit only `submission/`: `claim.json`, `Solution.lean`, and
  supporting modules under `submission/CommitGolfCandidate/`, and the optional README.
  No other repository directory is solver-editable. Everything else is the contract; preserve it.
- Submissions prove `CommitGolf.Certificate submission proofBytes commitCycles openingCycles`
  about a `CommitGolf.Submission` of machine images. The security-game scheme must be
  derived from those images; do not accept unrelated abstract functions or claimed timings.
- The score is `(commitCycles + openingCycles) * proofBytes` for a full commitment
  and one opening of 128 leaves. Binding and hiding target 120 bits; leaves are 2,048 bits.
- `Oracle.lean` fixes a 512→256 compression function and 1,600-bit permutation. Both public
  syscalls cost eight abstract cycles. Queries and cycles are separate accounting systems.
- Historical baselines are preserved but excluded from compilation and submission imports.
- Build with `lake build CommitGolf CommitGolfTests`.
  Verify with `bash scripts/setup.sh` and `python3 scripts/run.py` on supported Linux.
- Do not claim verification without a successful verifier run. `#print axioms` is not enough: it
  trusts declarations added with kernel checking disabled.
- Yukon handles submission PRs and promotions.
- When changing the contract, keep `RULES.md` concise and the repository minimal. Keep the Lean
  statements commented so that each file reads on its own, and refresh the line anchors in
  `RULES.md` when line numbers move.
