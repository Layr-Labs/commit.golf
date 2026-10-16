# Agent instructions

- Solvers edit only `submission/`: `claim.json`, `Solution.lean` and `CommitGolfCandidate/`.
  Everything else is the contract (`RULES.md`, the Lean statements in `CommitGolf/`, the baseline,
  `verifier/`, the scripts, the workflow and the Lean project pins); preserve it.
- A submission proves `CommitGolf.Certificate scheme proofBytes checkCalls`. The leaderboard is the
  Pareto frontier of `(proofBytes, checkCalls)`, lower being better in both.
- Build with `lake build CommitGolf CommitGolfBaseline CommitGolfTests`. Verify with
  `bash scripts/setup.sh` and `python3 scripts/run.py` on a supported Linux host.
- Do not claim verification without a successful verifier run. `#print axioms` is not enough: it
  trusts declarations added with kernel checking disabled.
- Yukon handles submission PRs and promotions.
- When changing the contract, keep `RULES.md` concise and keep its "Decisions" section current;
  keep the repository minimal. Keep the Lean statements commented so that each file reads on its
  own, and refresh the line anchors in `RULES.md` when line numbers move.
