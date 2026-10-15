# Agent instructions

- The contract is at the root: `RULES.md` is the single rules document, and `CommitGolf/` holds
  the Lean statements. Preserve them and the Lean project pins in submissions.
- A submission is a `CommitGolf.Scheme`, two claimed scores `(proofBytes, checkCalls)`, and a proof
  of `CommitGolf.Certificate scheme proofBytes checkCalls`. The leaderboard is the Pareto frontier of
  the two scores, lower being better in both.
- Build with `lake build CommitGolf CommitGolfBaseline CommitGolfTests`.
- The submission harness is not set up yet; do not claim verification without a kernel-checked
  certificate whose axioms are only `propext`, `Classical.choice` and `Quot.sound`.
- Yukon handles submission PRs and promotions.
- When changing the contract, keep `RULES.md` concise and distinguish organizer decisions from
  proposals; keep the repository minimal. Keep the Lean statements commented so that each file
  reads on its own, and refresh the line anchors in `RULES.md` when line numbers move.
