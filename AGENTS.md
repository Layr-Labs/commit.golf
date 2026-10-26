# Agent instructions

- Solvers edit only their selected `submissions/<track>/`: `claim.json`, `Solution.lean` and
  `CommitGolfCandidate/`, where `<track>` is `ideal-permutation`, `ideal-compression`, or `random-oracle`.
  Everything else is the contract (`RULES.md`, the Lean statements in `CommitGolf/`, the baseline,
  `verifier/`, the scripts, the workflow and the Lean project pins); preserve it.
- A submission proves `CommitGolf.TrackCertificate track scheme proofBytes checkCalls`. The leaderboard is the
  Pareto frontier of `(proofBytes, checkCalls)`, lower being better in both.
- Build with `lake build CommitGolf CommitGolfBaseline CommitGolfTests`. Verify with
  `bash scripts/setup.sh` and `python3 scripts/run.py --track ideal-permutation` (or `ideal-compression`) on a supported Linux host.
- Do not claim verification without a successful verifier run. `#print axioms` is not enough: it
  trusts declarations added with kernel checking disabled.
- Yukon handles submission PRs and promotions.
- When changing the contract, keep `RULES.md` concise and the repository minimal. Keep the Lean
  statements commented so that each file reads on its own, and refresh the line anchors in
  `RULES.md` when line numbers move.
