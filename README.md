# commit.golf

Optimize a **vector commitment scheme** under the [draft rules](RULES.md), in four
tracks: **ideal permutation**, **ideal compression**, **variable-input, fixed-output random oracle**, or **ideal XOF**. A scheme declares a finite collection
of independent instances of its track's primitive.

Schemes commit to `2^24` entries of 32 bytes. Each track ranks schemes on the Pareto frontier of
two worst-case scores for openings of 100 positions: **opening proof bytes** and **oracle calls
made by `check`**. Every scheme proves perfect completeness and position binding error at most
`q / 2^128` against adversaries making `q` calls across the declared family.

## Contract and baselines

`RULES.md` states the rules; `CommitGolf/` holds the Lean contract. `CommitGolf/Oracle/` defines
the primitives and their families. `CommitGolfBaseline/` contains binary Merkle baselines:
one 1600-bit permutation, or one 512-to-256-bit compression function. Both claim
`(76800 bytes, 2400 calls)` with certificates in their respective proof modules.

```sh
lake exe cache get
# Build and check either baseline submission independently:
lake build IdealPermutation
lake build IdealCompression

# Check the RO and XOF models (certified baselines are not yet implemented):
lake build RandomOracleFixedOutputModel
lake build IdealXofModel

# Build both baseline libraries and all regression tests:
lake build CommitGolf CommitGolfBaseline CommitGolfTests
```

The `random-oracle-fixed-output` track accepts any finite bitstring, including the empty string. Each instance
chooses a positive fixed output width. Fresh inputs get independent uniform answers; repeated
inputs reuse the same answer. Every query costs one call regardless of input length. The binding
game uses shared oracle state for every track and counts only adversary calls. A Lean equivalence
proof shows that the finite-domain tracks retain their original winning probabilities.
The model, eligibility checks, and verifier track selection are implemented. A certified Merkle
starter for this track is still pending; `RandomOracleFixedOutputModel` checks the model, not a submission.

The `ideal-xof` track accepts `(input, outputBits)` queries and returns a prefix of a random
bit stream specific to that input. Longer outputs extend shorter outputs; zero-length output
is allowed. Every request costs one call, regardless of output length. Internal uniform bit
sampling uses VCVio's cached random oracle and does not add public calls. `IdealXofModel`
checks the model; a certified baseline is not supplied yet.

## Submitting

Edit `submissions/ideal-permutation/` or `submissions/ideal-compression/`. Each directory starts
with its track's baseline, with `claim.json` and `Solution.lean`. Optional supporting modules go
in that directory's `CommitGolfCandidate/`. The certificate enforces the selected track. Custom random-oracle-fixed-output submissions use
`submissions/random-oracle-fixed-output/` and `--track random-oracle-fixed-output`; no certified starter is supplied there yet. XOF submissions use
`submissions/ideal-xof/` and `--track ideal-xof`, also without a certified starter.

On Linux with Landlock and user systemd:

```sh
bash scripts/setup.sh
python3 scripts/run.py --track ideal-permutation
python3 scripts/run.py --track ideal-compression
```

Omitting `--track` from `scripts/run.py` selects `ideal-permutation` for compatibility with the
existing workflow. The workflows are unchanged; compression verification is selected locally.
The runner writes the selected track and its scores to `scripts/score.json`.

## License

See `LICENSE` and `THIRD_PARTY_NOTICES.md`.
