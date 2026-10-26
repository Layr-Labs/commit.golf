# commit.golf · rules

Design a vector commitment scheme in one of the ideal-oracle tracks below, with the syntax and security notions of Chapter 18 of [CY24] (Chiesa and Yogev, *[Building Cryptographic Proofs from Hash Functions](https://github.com/hash-based-snargs-book/hash-based-snargs-book)*). Schemes are ranked on the Pareto frontier of two scores for openings of 100 positions, lower being better in both:

- **proof size**: bytes in the opening proof;
- **verification cost**: oracle calls made by `check`.

## Model

([Parameters](CommitGolf/Parameters.lean), [Oracle family](CommitGolf/Oracle/Family.lean))

| Constant          | Value          |
| ----------------- | -------------- |
| `DIGEST_BYTES`    | 32             |
| `LENGTH` (`ℓ`)    | 2^24           |
| `BATCH`           | 100            |
| `SECURITY_BITS`   | 128            |
| `COMMIT_BUDGET`   | 100 · ℓ calls  |
| `OPEN_BUDGET(k)`  | 100 · k calls  |
| `CHECK_BUDGET(k)` | 100 · k calls  |

A scheme declares a finite, nonempty collection of independent oracle instances. Each instance
has its own dimensions, measured in bits, fixed before any experiment:

- **Ideal permutation:** a uniform bijection of `{0,1}^n`, with `n > 0`. Forward and inverse
  queries are available. See [IdealPermutation](CommitGolf/Oracle/IdealPermutation.lean).
- **Ideal compression:** a uniform function `{0,1}^n → {0,1}^m`, with `0 < m < n`. Only forward
  queries are available; collisions are allowed. See
  [IdealCompression](CommitGolf/Oracle/IdealCompression.lean).
- **Random oracle:** a function `{0,1}* → {0,1}^m`, with `m > 0`, on arbitrary finite bitstrings
  including the empty string. Distinct inputs have independent uniform outputs. See
  [RandomOracle](CommitGolf/Oracle/RandomOracle.lean).

Every instance must belong to the selected track. Queries identify their instance; distinct
instances are independent even when their dimensions match. Repeated inputs to the same
instance return the same answer. All parties share the same realization `H` of the collection.
Every query costs one **call**, regardless of input length or bit widths, including repeats and inverse queries;
private coins and local computation are free. `X^H` denotes `X` with access to this collection.

- A message is `m ∈ Σ^ℓ` with `Σ = {0,1}^256`. For positions `I ⊆ [ℓ] = {0, …, ℓ−1}`, `m[I] ∈ Σ^I` is its restriction.
- A commitment is `rt ∈ {0,1}^256`; a proof `pf` is a byte string of `|pf|` bytes.

## Scheme

([Lean](CommitGolf/Scheme.lean#L10-L24))

- `commit^H(m) → (rt, td)`, probabilistic, where the opening trapdoor `td` has any type;
- `opening^H(td, I) → pf`, probabilistic;
- `check^H(rt, I, a, pf) → {0, 1}` for `a ∈ Σ^I`, deterministic.

The **honest run** ([Lean](CommitGolf/Honest.lean#L23-L28)) on `(H, m, I)` is `(rt, td) ← commit^H(m)`, `pf ← opening^H(td, I)`, `b := check^H(rt, I, m[I], pf)`.

## Statements

A certificate for `(proofBytes, checkCalls)` ([Lean](CommitGolf/Statements.lean#L46-L53)) proves five statements. The first four hold in the honest run for every realization `H`, `m`, `I`, and all coins:

1. **Completeness** ([Lean](CommitGolf/Statements.lean#L15-L18)): `b = 1`.
2. **Honest budgets** ([Lean](CommitGolf/Statements.lean#L20-L26)): `commit`, `opening`, and `check` make at most `COMMIT_BUDGET`, `OPEN_BUDGET(|I|)`, and `CHECK_BUDGET(|I|)` calls, respectively.
3. **Proof size** ([Lean](CommitGolf/Statements.lean#L28-L31)): if `|I| = BATCH`, then `|pf| ≤ proofBytes`.
4. **Verification cost** ([Lean](CommitGolf/Statements.lean#L33-L36)): if `|I| = BATCH`, then `check` makes at most `checkCalls` calls.
5. **Binding** ([Lean](CommitGolf/Statements.lean#L38-L42)): for every adversary `A` and every `q ≥ 1`,

   `Pr[A wins and makes at most q calls] ≤ q / 2^SECURITY_BITS`.

In the **binding game** ([Lean](CommitGolf/Binding.lean)), finite-domain instances are sampled independently and uniformly. Random-oracle answers are sampled on first query and cached across the adversary and both checks. `A` ([Lean](CommitGolf/Binding.lean#L26-L28)), probabilistic and computationally unbounded, queries the declared collection and outputs `(rt, I₀, a₀, pf₀, I₁, a₁, pf₁)` ([Lean](CommitGolf/Binding.lean#L16-L24)). It **wins** ([Lean](CommitGolf/Binding.lean#L35-L39)) if `check^H(rt, I₀, a₀, pf₀) = check^H(rt, I₁, a₁, pf₁) = 1` and `a₀[i] ≠ a₁[i]` for some `i ∈ I₀ ∩ I₁` ([Lean](CommitGolf/Binding.lean#L30-L33)). Only `A`'s calls count.

## Submission

Select `submissions/ideal-permutation/`, `submissions/ideal-compression/`, or `submissions/random-oracle/`. It holds `claim.json`,
with `proofBytes` and `checkCalls`, and `Solution.lean`, with optional modules under
`CommitGolfCandidate/`. `Solution.lean` defines `CommitGolf.Challenge.submission : Scheme` and
proves `CommitGolf.Challenge.certificate : TrackCertificate track submission proofBytes checkCalls`.
The track certificate proves the five statements and that all declared instances belong to the
selected track. The trusted verifier selects `track`; the submission cannot override it.
Allowed imports are `CommitGolf`, `CommitGolfBaseline`, and the pinned dependencies (Lean,
Batteries, Mathlib, VCVio). Permutation and compression have certified baseline examples; the random-oracle starter is pending.

The [verifier](verifier/verify.py) runs Lean's [`comparator`](https://github.com/leanprover/comparator) in a sandbox. It checks that the proof passes Lean's kernel with every declaration replayed, that it proves exactly the [challenge](verifier/Challenge.lean.in), and that it uses only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

```sh
lake build CommitGolf CommitGolfBaseline CommitGolfTests   # build
bash scripts/setup.sh && python3 scripts/run.py --track ideal-permutation # verify (Linux, Landlock, user systemd)
```

## Baselines

Both use the binary Merkle tree with unpruned paths, scoring `(76800, 2400)`:

- [Permutation](CommitGolfBaseline/Merkle.lean): `C(L, R)` is the low 256 bits of
  `π(0¹⁰⁸⁸ ‖ L ‖ R)`, for one 1600-bit permutation. Its certificate is in
  [MerkleProof](CommitGolfBaseline/MerkleProof/Certificate.lean).
- [Compression](CommitGolfBaseline/Compression.lean): `C(L, R) = H(L ‖ R)`, for one 512-to-256-bit
  ideal compression function. Its certificate is in
  [CompressionProof](CommitGolfBaseline/CompressionProof/Certificate.lean).
