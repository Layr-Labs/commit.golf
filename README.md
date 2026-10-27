# commit.golf

Optimize a **vector commitment scheme** under the [draft rules](RULES.md), in four
tracks: **ideal permutation**, **ideal compression**, **variable-input, fixed-output random oracle**, or **ideal XOF**. A scheme declares a finite collection
of independent instances of its track's primitive.

Schemes commit to `2^24` entries of 32 bytes. Each track minimizes the product of
two certified worst-case bounds for openings of 100 positions: **opening proof bytes** and **oracle calls
made by `check`**. Both factors are recorded as metrics. Every scheme proves perfect completeness and position binding error at most
`q / 2^128` against adversaries making `q` calls across the declared family.

## Contract and baselines

`RULES.md` states the rules; `CommitGolf/` holds the Lean contract. `CommitGolf/Oracle/` defines
the primitives and their families. Each `submissions/<track>/CommitGolfCandidate/` contains its own Merkle construction and proofs:
one 1600-bit permutation, one 512-to-256-bit compression function, a fixed-output
random oracle with 256-bit outputs, or an XOF requesting 256-bit outputs. All four claim
`(76800 bytes, 2400 calls)` with certificates in their respective proof modules.

```sh
lake exe cache get
# Build and check each certified baseline submission independently:
lake build IdealPermutation
lake build IdealCompression
lake build RandomOracleFixedOutput
lake build IdealXof

# Check the oracle models independently:
lake build RandomOracleFixedOutputModel
lake build IdealXofModel

# Build the contract and regression tests:
lake build CommitGolf CommitGolfTests
```

The `random-oracle-fixed-output` track accepts any finite bitstring, including the empty string. Each instance
chooses a positive fixed output width. Fresh inputs get independent uniform answers; repeated
inputs reuse the same answer. Every query costs one call regardless of input length. The binding
game uses shared oracle state for every track and counts only adversary calls. A Lean equivalence
proof shows that the finite-domain tracks retain their original winning probabilities.
The certified Merkle starter uses 512-bit encodings of child pairs and 256-bit outputs.
`RandomOracleFixedOutput` builds its submission; `RandomOracleFixedOutputModel` checks only the model.

The `ideal-xof` track accepts `(input, outputBits)` queries and returns a prefix of a random
bit stream specific to that input. Longer outputs extend shorter outputs; zero-length output
is allowed. Every request costs one call, regardless of output length. Internal uniform bit
sampling uses VCVio's cached random oracle and does not add public calls. `IdealXofModel`
checks the model; `IdealXof` builds the certified Merkle starter, which requests 256-bit digests.

## Submitting

Edit `submissions/ideal-permutation/`, `submissions/ideal-compression/`,
`submissions/random-oracle-fixed-output/`, or `submissions/ideal-xof/`. Each directory starts
with `claim.json`, `Solution.lean`, and the complete baseline source and proofs in
`CommitGolfCandidate/`. These files are editable independently of every other track. The certificate enforces the selected track. Pass the same track name to `--track` when verifying.

On Linux with Landlock and user systemd:

```sh
bash scripts/setup.sh
bash scripts/benchmark.sh --track ideal-permutation
bash scripts/benchmark.sh --track ideal-compression
bash scripts/benchmark.sh --track random-oracle-fixed-output
bash scripts/benchmark.sh --track ideal-xof
```

Omitting `--track` from `scripts/benchmark.sh` selects `ideal-permutation` for compatibility with the
existing workflow. Each track has a dispatch workflow calling the same isolated verifier job.
The runner writes the product score, selected track, and both metrics to
`scripts/scores/<track>/score.json`.

## License

See `LICENSE` and `THIRD_PARTY_NOTICES.md`.

## Yukon

`benchmark.json` declares all four tracks on one shared branch, each with a certified baseline
submission. Yukon validates each baseline during import.

Each track permits edits only
in its corresponding `submissions/<track>/` directory. After import, use:

```sh
yukon setup --track ideal-permutation
yukon run --track ideal-permutation
yukon submit --track ideal-permutation
```

Substitute another declared track name to select it. `yukon switch <track>` changes only Yukon
selection; it preserves your Git branch, HEAD, index, and worktree. Yukon owns submission PRs
and promotions; do not manually merge submission PRs. Failed verification produces no score.
Use submission notes for reproducible context and GitHub Discussions for partial research;
remove secrets and private data before posting.
