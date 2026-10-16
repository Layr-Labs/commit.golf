# commit.golf · rules

Design a vector commitment scheme in the ideal permutation model, as in Chapter 18 of [CY24] (Chiesa and Yogev, *[Building Cryptographic Proofs from Hash Functions](https://github.com/hash-based-snargs-book/hash-based-snargs-book)*). Schemes are ranked on the Pareto frontier of two scores for openings of 100 positions, lower being better in both:

- **proof size**: bytes in the opening proof;
- **verification cost**: permutation calls made by `check`.

## Model

([Lean](CommitGolf/Parameters.lean), [Lean](CommitGolf/Oracle.lean))

| Constant          | Value          |
| ----------------- | -------------- |
| `WIDTH`           | 1600 bits      |
| `DIGEST_BYTES`    | 32             |
| `LENGTH` (`ℓ`)    | 2^24           |
| `BATCH`           | 100            |
| `SECURITY_BITS`   | 128            |
| `COMMIT_BUDGET`   | 100 · ℓ calls  |
| `OPEN_BUDGET(k)`  | 100 · k calls  |
| `CHECK_BUDGET(k)` | 100 · k calls  |

- `π` is a permutation of `{0,1}^1600`. Each query to `π` or `π⁻¹` is one **call**; local computation is free.
- A message is `m ∈ Σ^ℓ` with `Σ = {0,1}^256`. For positions `I ⊆ [ℓ]`, `m[I] ∈ Σ^I` is its restriction.
- A commitment is `rt ∈ {0,1}^256`; a proof `pf` is a byte string, of length `|pf|`.

## Scheme

([Lean](CommitGolf/Scheme.lean#L10-L22))

- `commit^π(m) → (rt, td)`, probabilistic, where `td` is any opening trapdoor;
- `opening^π(td, I) → pf`, probabilistic;
- `check^π(rt, I, a, pf) → {0, 1}` for `a ∈ Σ^I`, deterministic.

The **honest run** ([Lean](CommitGolf/Honest.lean#L24-L29)) on `(π, m, I)` is `(rt, td) ← commit^π(m)`, `pf ← opening^π(td, I)`, `b := check^π(rt, I, m[I], pf)`.

## Statements

A certificate for `(proofBytes, checkCalls)` ([Lean](CommitGolf/Statements.lean#L46-L53)) proves five statements. The first four hold in the honest run for every `π`, `m`, `I`, and all coins:

1. **Completeness** ([Lean](CommitGolf/Statements.lean#L15-L18)): `b = 1`.
2. **Honest budgets** ([Lean](CommitGolf/Statements.lean#L20-L26)): `commit`, `opening`, and `check` make at most `COMMIT_BUDGET`, `OPEN_BUDGET(|I|)`, and `CHECK_BUDGET(|I|)` calls.
3. **Proof size** ([Lean](CommitGolf/Statements.lean#L28-L31)): if `|I| = BATCH`, then `|pf| ≤ proofBytes`.
4. **Verification cost** ([Lean](CommitGolf/Statements.lean#L33-L36)): if `|I| = BATCH`, then `check` makes at most `checkCalls` calls.
5. **Binding** ([Lean](CommitGolf/Statements.lean#L38-L42)): for every adversary `A` and every `q ≥ 1`,

   `Pr[A wins and makes at most q calls] ≤ q / 2^128`.

In the **binding game** ([Lean](CommitGolf/Binding.lean#L40-L45)), `π` is uniform over all permutations, and `A` ([Lean](CommitGolf/Binding.lean#L25-L27)), computationally unbounded, queries `π` and `π⁻¹` and outputs `(rt, I₀, a₀, pf₀, I₁, a₁, pf₁)` ([Lean](CommitGolf/Binding.lean#L15-L23)). It **wins** ([Lean](CommitGolf/Binding.lean#L34-L38)) if `check^π(rt, I₀, a₀, pf₀) = check^π(rt, I₁, a₁, pf₁) = 1` and `a₀[i] ≠ a₁[i]` for some `i ∈ I₀ ∩ I₁` ([Lean](CommitGolf/Binding.lean#L29-L32)). Only `A`'s calls count.

Equivalently, with `ε(q)` the largest winning probability using at most `q` calls: `q / ε(q) ≥ 2^128` for all `q ∈ [1, 2^128]`. A birthday collision on `n`-bit digests gives `ε(q) ≈ q² / 2^n`, so `n ≈ 256`.

## Submission

The directory `submission/` holds `claim.json`, with `proofBytes` and `checkCalls`, and `Solution.lean`, with optional modules under `CommitGolfCandidate/`. `Solution.lean` defines `CommitGolf.Challenge.submission : Scheme` and proves `CommitGolf.Challenge.certificate : Certificate submission proofBytes checkCalls`. It may import `CommitGolf`, `CommitGolfBaseline`, Mathlib, VCVio, and Lean's standard libraries. The [example](submission/Solution.lean) submits the baseline.

The [verifier](verifier/verify.py), ported from sig.golf, runs Lean's [`comparator`](https://github.com/leanprover/comparator) in a sandbox. It checks that the proof passes Lean's kernel with every declaration replayed, that it proves exactly the [challenge](verifier/Challenge.lean.in), and that it uses only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

A verified submission enters the leaderboard unless an existing entry is at least as good on both scores.

```sh
lake build CommitGolf CommitGolfBaseline CommitGolfTests   # build
bash scripts/setup.sh && python3 scripts/run.py            # verify (Linux, Landlock, user systemd)
```

## Baseline

[`CommitGolfBaseline/Merkle.lean`](CommitGolfBaseline/Merkle.lean): the binary Merkle tree with `C(L, R) = trunc₂₅₆ π(0¹⁰⁸⁸ ‖ L ‖ R)` and unpruned paths, scoring `(76800, 2400)`. [`CommitGolfBaseline/MerkleProof/`](CommitGolfBaseline/MerkleProof) proves its certificate.

## Decisions

All parameters above are agreed with the organizers. Perfect completeness, a deterministic `check`, and binding counting only the adversary's calls follow [CY24]. The 32-byte commitment rules out Merkle caps and multi-root commitments.

## Known limitations

- **Binding, not extractability** [CY24, §18.5], and **no hiding** [CY24, §18.6].
- **One commitment, no preprocessing, classical adversaries.**
- **Ideal model.** A `check` that accepts anything when `π` maps a hard-coded state to a hard-coded Keccak-f output is binding for a random `π` but not for Keccak-f. Submissions are reviewed by hand for such backdoors.
