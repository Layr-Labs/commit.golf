# Agent instructions

- Solvers edit only `submission/`: `claim.json`, `Solution.lean`, and
  supporting modules under `submission/CommitGolfCandidate/`, and the optional README.
  No other repository directory is solver-editable. Everything else is the contract; preserve it.
- Submissions prove `CommitGolf.Certificate scheme proofBytes checkCalls`,
  requiring hiding. `Oracle.lean` fixes the 512→256 compression function and
  1,600-bit permutation for every scheme. Historical baselines are preserved but
  excluded from compilation and submission imports.
- Binding and hiding target 120 bits. Scores and size parameters still await the next
  consolidation step. Do not claim RISC-V cycle scoring is implemented.
- Build with `lake build CommitGolf CommitGolfTests`.
  Verify with `bash scripts/setup.sh` and `python3 scripts/run.py` on supported Linux.
- Do not claim verification without a successful verifier run. `#print axioms` is not enough: it
  trusts declarations added with kernel checking disabled.
- Yukon handles submission PRs and promotions.
- When changing the contract, keep `RULES.md` concise and the repository minimal. Keep the Lean
  statements commented so that each file reads on its own, and refresh the line anchors in
  `RULES.md` when line numbers move.
