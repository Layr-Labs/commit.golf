# Agent instructions

- Solvers edit only their selected track: `submission/` (product), `submission-pareto/` (Pareto),
  `submission-commit-golf-64-32-product/`, `submission-commit-golf-64-32-pareto/`,
  `submission-commit-golf-96-32-product/`, `submission-commit-golf-96-32-pareto/`,
  `submission-commit-golf-oracle-rounds-pareto/`, or `submission-commit-golf-work-span-pareto/`:
  `claim.json`, `programs.json`, `Solution.lean`, and
  supporting modules under the selected directory’s `CommitGolfCandidate/`, and the optional README.
  No other repository directory is solver-editable. Everything else is the contract; preserve it.
- Submissions prove `CommitGolf.Certificate submission proofBytes commitCycles openingCycles`
  about a `CommitGolf.Submission` of machine images. The security-game scheme must be
  derived from those images; do not accept unrelated abstract functions or claimed timings.
- The oracle-rounds and work/span tracks use their respective `CommitGolfDepth` full
  certificates, adding rounds or work/span bounds to the inherited security requirements.
  Their schema-v2 artifacts bind execution modes as well as bytes. Both rank three
  objectives by Pareto minimization; see `docs/depth-rules.md` for fields and prices.
  Resource-only regression clients under `verifier/tests/fixtures/` are not scored submissions.
- `programs.json` delivers the instruction bytes, embedded data and ABI. The verifier generates
  `CommitGolf.Artifact.submission` (or `depthSubmission` on depth tracks);
  `submission_matches_artifact` must prove that the certified submission equals this exact value. The generated artifact is not a comparator definition hole.
- The product score is `(commitCycles + openingCycles) * proofBytes` for a full commitment
  and one opening of 128 leaves. Binding and hiding target 120 bits; leaves are 2,048 bits.
- The Pareto track minimizes `[commitCycles + openingCycles, proofBytes]` independently
  under the same certificate and numeric admission limits. Run it with `python3 scripts/run.py --track pareto`.
- `Oracle.lean` uses a 512→256 compression function (768→256 on the `commit-golf-96-32-*` tracks)
  and 1,600-bit permutation. Compression
  costs eight cycles in every track. Forward and inverse permutation calls cost eight on the
  original and depth tracks, and 30 on the four `commit-golf-64-32-*` and
  `commit-golf-96-32-*` tracks. The verifier selects the
  trusted width and cost in its isolated contract; the repository's `Parameters.lean`
  retains the 512-bit compression input and eight-cycle permutation price.
  Queries and cycles are separate accounting systems; every public call consumes one query.
- Never weaken the comparator to accept a missing or incomplete certificate.
  Full-score workflows require the same complete certificate. For a contract change,
  the PR gate verifies the original product and Pareto baselines and every new-track
  baseline whose submission root exists. Changed roots also require verification,
  including deleted or replaced roots. Submission-only same-repository `submissions/*`
  branches delegate verification to Yukon; contract changes override that delegation.
- Historical baselines are preserved but excluded from compilation and submission imports.
- Build with `lake build CommitGolf CommitGolfTests`.
  Verify with `bash scripts/setup.sh` and `python3 scripts/run.py` on supported Linux.
- Do not claim verification without a successful verifier run. `#print axioms` is not enough: it
  trusts declarations added with kernel checking disabled.
- Yukon handles submission PRs and promotions.
- When changing the contract, keep `RULES.md` concise and the repository minimal. Keep the Lean
  statements commented so that each file reads on its own, and refresh the line anchors in
  `RULES.md` when line numbers move.

- Follow [ArkLib's writing guidance](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/wiki/writing.md)
  and the applicable [contribution guidance](https://github.com/Verified-zkEVM/ArkLib/blob/main/CONTRIBUTING.md#description)
  for all documentation: READMEs, rules and design notes, code docstrings and comments,
  commit messages, PR and issue descriptions, and review text. Preserve mathematical
  claims, hypotheses, uncertainty and requirement strength. Describe the current code,
  cite accessible sources, and keep session logs out of reference documentation.
  Revise clarity or accuracy problems; leave clear, correct text alone.
