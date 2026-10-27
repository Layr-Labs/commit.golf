# commit.golf · rules

Design a vector commitment scheme in the ideal permutation model, with the syntax and security notions of Chapter 18 of [CY24] (Chiesa and Yogev, *[Building Cryptographic Proofs from Hash Functions](https://github.com/hash-based-snargs-book/hash-based-snargs-book)*). Schemes are ranked on the Pareto frontier of two scores for openings of 100 positions, lower being better in both:

- **proof size**: bytes in the opening proof;
- **verification cost**: permutation calls made by `check`.

## Model

([Parameters](CommitGolf/Parameters.lean), [Oracle](CommitGolf/Oracle.lean))

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

- `π` is a permutation of `{0,1}^1600`. Each query to `π` or `π⁻¹` is one **call**; local computation is free. `X^π` denotes `X` with access to `π` and `π⁻¹`.
- A message is `m ∈ Σ^ℓ` with `Σ = {0,1}^256`. For positions `I ⊆ [ℓ] = {0, …, ℓ−1}`, `m[I] ∈ Σ^I` is its restriction.
- A commitment is `rt ∈ {0,1}^256`; a proof `pf` is a byte string of `|pf|` bytes.

## Scheme

([Lean](CommitGolf/Scheme.lean#L10-L22))

- `commit^π(m) → (rt, td)`, probabilistic, where the opening trapdoor `td` has any type;
- `opening^π(td, I) → pf`, probabilistic;
- `check^π(rt, I, a, pf) → {0, 1}` for `a ∈ Σ^I`, deterministic.

The **honest run** ([Lean](CommitGolf/Honest.lean#L23-L28)) on `(π, m, I)` is `(rt, td) ← commit^π(m)`, `pf ← opening^π(td, I)`, `b := check^π(rt, I, m[I], pf)`.

## Statements

A certificate for `(proofBytes, checkCalls)` ([Lean](CommitGolf/Statements.lean#L46-L53)) proves five statements. The first four hold in the honest run for every `π`, `m`, `I`, and all coins:

1. **Completeness** ([Lean](CommitGolf/Statements.lean#L15-L18)): `b = 1`.
2. **Honest budgets** ([Lean](CommitGolf/Statements.lean#L20-L26)): `commit`, `opening`, and `check` make at most `COMMIT_BUDGET`, `OPEN_BUDGET(|I|)`, and `CHECK_BUDGET(|I|)` calls, respectively.
3. **Proof size** ([Lean](CommitGolf/Statements.lean#L28-L31)): if `|I| = BATCH`, then `|pf| ≤ proofBytes`.
4. **Verification cost** ([Lean](CommitGolf/Statements.lean#L33-L36)): if `|I| = BATCH`, then `check` makes at most `checkCalls` calls.
5. **Binding** ([Lean](CommitGolf/Statements.lean#L38-L42)): for every adversary `A` and every `q ≥ 1`,

   `Pr[A wins and makes at most q calls] ≤ q / 2^SECURITY_BITS`.

In the **binding game** ([Lean](CommitGolf/Binding.lean#L39-L44)), `π` is uniform over all permutations, and `A` ([Lean](CommitGolf/Binding.lean#L25-L26)), probabilistic and computationally unbounded, queries `π` and `π⁻¹` and outputs `(rt, I₀, a₀, pf₀, I₁, a₁, pf₁)` ([Lean](CommitGolf/Binding.lean#L15-L23)). It **wins** ([Lean](CommitGolf/Binding.lean#L33-L37)) if `check^π(rt, I₀, a₀, pf₀) = check^π(rt, I₁, a₁, pf₁) = 1` and `a₀[i] ≠ a₁[i]` for some `i ∈ I₀ ∩ I₁` ([Lean](CommitGolf/Binding.lean#L28-L31)). Only `A`'s calls count.

## Submission

The directory `submission/` holds `claim.json`, with `proofBytes` and `checkCalls`, and `Solution.lean`, with optional modules under `CommitGolfCandidate/`. `Solution.lean` defines `CommitGolf.Challenge.submission : Scheme` and proves `CommitGolf.Challenge.certificate : Certificate submission proofBytes checkCalls`. It may import `CommitGolf`, `CommitGolfBaseline`, and the pinned dependencies (Lean, Batteries, Mathlib, VCVio). The [example](submission/Solution.lean) submits the baseline.

The [verifier](verifier/verify.py) runs Lean's [`comparator`](https://github.com/leanprover/comparator) in a sandbox. It checks that the proof passes Lean's kernel with every declaration replayed, that it proves exactly the [challenge](verifier/Challenge.lean.in), and that it uses only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

```sh
lake build CommitGolf CommitGolfBaseline CommitGolfTests   # build
bash scripts/setup.sh && python3 scripts/run.py            # verify (Linux, Landlock, user systemd)
```

## Baseline

[`CommitGolfBaseline/Merkle.lean`](CommitGolfBaseline/Merkle.lean): the binary Merkle tree with `C(L, R)` the low 256 bits of `π(0¹⁰⁸⁸ ‖ L ‖ R)`, and unpruned paths, scoring `(76800, 2400)`. [`CommitGolfBaseline/MerkleProof/`](CommitGolfBaseline/MerkleProof) proves its certificate.
