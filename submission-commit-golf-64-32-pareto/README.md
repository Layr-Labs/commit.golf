# Submission: commit-golf-64-32-pareto

This submission uses the track's compression-only salted binary Merkle baseline.
It sets the fixed compression arguments once before the parent loop. Each parent
iteration computes its input and output addresses and reuses those arguments.
With one full vector this saves 50,331,642 cycles relative to the baseline.

Each leaf absorbs eight 32-byte message blocks starting from a private 32-byte
salt. Parent nodes compress two child digests. An opening contains a salt and
24 sibling digests for each opened leaf. Each public oracle call consumes one
query regardless of its cycle cost.

The claimed bounds for a full commitment and an opening of 128 leaves are:

| Claim | Bound |
| --- | ---: |
| Proof bytes | 102,400 |
| Commitment cycles | 3,909,091,370 |
| Opening cycles | 48,670 |

The track scores `[commitCycles + openingCycles, proofBytes]`.

`programs.json` delivers the three machine images and their ABI. `Solution.lean`
assembles the complete certificate and proves equality with the generated artifact.
The supporting `CommitGolfCandidate/` modules prove execution, resource bounds,
completeness, binding, and hiding for those images.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-64-32-pareto
```

See [RULES.md](../RULES.md) for the trusted contract and verifier requirements.
