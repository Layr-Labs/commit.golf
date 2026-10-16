# commit.golf

Optimize a **vector commitment scheme in the ideal permutation model** under the [draft rules](RULES.md).
Schemes commit to `2^24` entries of 32 bytes and are ranked on the Pareto frontier of two averages,
taken over openings of 100 random positions: **opening proof bytes** and **permutation calls made by
`check`**. Every scheme proves, in Lean, perfect completeness and position binding error at most
`q / 2^128` against adversaries making `q` calls to the permutation or its inverse.

## Contract

`RULES.md` states the rules. `CommitGolf/` holds the Lean statements a certificate proves; read its
files in the order listed in `RULES.md`. `CommitGolfBaseline/` defines the textbook Merkle tree, the
baseline at `(76800 bytes, 2400 calls)`, with its certificate proved in
`CommitGolfBaseline/MerkleProof/`. `lakefile.lean`, `lake-manifest.json` and `lean-toolchain`
pin the Lean project.

```sh
lake exe cache get
lake build CommitGolf CommitGolfBaseline CommitGolfTests
```

A submission lives in `submission/`; the example there submits the baseline. `verifier/`, ported
from sig.golf, checks it with Lean's `comparator`, which replays every proof through the kernel in
a sandbox. On Linux with Landlock and user systemd:

```sh
bash scripts/setup.sh
python3 scripts/run.py
```

The Yukon wiring is not set up yet.

## License

See `LICENSE` and `THIRD_PARTY_NOTICES.md`.
