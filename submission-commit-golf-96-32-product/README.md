# Initial submission: commit-golf-96-32-product

This is a salted binary Merkle baseline over the track's 96→32-byte compression
oracle. Compression costs eight cycles; forward and inverse permutation calls
cost 30. The programs use compression only.

Each leaf absorbs eight 32-byte message blocks starting from a private 32-byte
salt. Parent nodes combine two child digests. Each 64-byte binary encoding is
padded with 32 zero bytes before calling the actual 96-byte oracle. The padding
is injective, so the collision reduction retains both input digests.

The assembly adapter saves the third 32-byte block, zeroes it for the query, and
restores it afterward. Its call and return add 16 ordinary instructions per
compression compared with the original baseline. Those instructions are included
in the cycle claims. Every public oracle call still consumes one query.

The claimed bounds for a full commitment and an opening of 128 leaves are:

| Claim | Bound |
| --- | ---: |
| Proof bytes | 102,400 |
| Commitment cycles | 6,375,342,100 |
| Opening cycles | 48,670 |

The product score is `(commitCycles + openingCycles) * proofBytes`.

`programs.json` delivers the three machine images and their ABI. `Solution.lean`
assembles the complete certificate and proves equality with the generated artifact.
The supporting `CommitGolfCandidate/` modules prove execution, resource bounds,
completeness, binding, and hiding for those images. `Padding96*.lean` covers the
wider input encoding, temporary memory changes, actual instruction trace, and costs.

From the repository root, on a supported Linux verifier host:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track commit-golf-96-32-product
```

See [RULES.md](../RULES.md) for the trusted contract and verifier requirements.
