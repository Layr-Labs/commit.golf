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
uses the dimensions below, measured in bits. Permutation, compression, and fixed-output RO
dimensions are fixed before the experiment; XOF output length is chosen per query:

- **Ideal permutation:** a uniform bijection of `{0,1}^n`, with `n > 0`. Forward and inverse
  queries are available. See [IdealPermutation](CommitGolf/Oracle/IdealPermutation.lean).
- **Ideal compression:** a uniform function `{0,1}^n → {0,1}^m`, with `0 < m < n`. Only forward
  queries are available; collisions are allowed. See
  [IdealCompression](CommitGolf/Oracle/IdealCompression.lean).
- **Random oracle:** a function `{0,1}* → {0,1}^m`, with `m > 0`, on arbitrary finite bitstrings
  including the empty string. Distinct inputs have independent uniform outputs. See
  [RandomOracleFixedOutput](CommitGolf/Oracle/RandomOracleFixedOutput.lean).
- **Ideal XOF:** each input in `{0,1}*` identifies an independent uniform bit stream. A query
  `(x, n)` returns its first `n` bits, in most-significant-bit order, for any `n ≥ 0`.
  Longer answers extend shorter ones. See [IdealXof](CommitGolf/Oracle/IdealXof.lean).

Every instance must belong to the selected track. Queries identify their instance; distinct
instances are independent even when their dimensions match. Repeated queries to the same
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

A certificate for `(proofBytes, checkCalls)` ([Lean](CommitGolf/Statements.lean#L69-L74)) proves five statements. The first four hold in the honest run for every realization `H`, `m`, `I`, and all coins:

1. **Completeness** ([Lean](CommitGolf/Statements.lean#L18-L20)): `b = 1`.
2. **Honest budgets** ([Lean](CommitGolf/Statements.lean#L23-L28)): `commit`, `opening`, and `check` make at most `COMMIT_BUDGET`, `OPEN_BUDGET(|I|)`, and `CHECK_BUDGET(|I|)` calls, respectively.
3. **Proof size** ([Lean](CommitGolf/Statements.lean#L31-L33)): if `|I| = BATCH`, then `|pf| ≤ proofBytes`.
4. **Verification cost** ([Lean](CommitGolf/Statements.lean#L36-L38)): if `|I| = BATCH`, then `check` makes at most `checkCalls` calls.
5. **Binding** ([Lean](CommitGolf/Statements.lean#L41-L47)): for every adversary `A` and every `q ≥ 1`,

   `Pr[A wins and makes at most q calls] ≤ q / 2^SECURITY_BITS`.

In the **binding game** ([Lean](CommitGolf/Binding.lean)), finite-domain instances are sampled independently and uniformly. Random-oracle answers and XOF stream bits are sampled when first needed and cached across the adversary and both checks. `A` ([Lean](CommitGolf/Binding.lean#L24-L26)), probabilistic and computationally unbounded, queries the declared collection and outputs `(rt, I₀, a₀, pf₀, I₁, a₁, pf₁)` ([Lean](CommitGolf/Binding.lean#L14-L22)). It **wins** ([Lean](CommitGolf/Statements.lean#L41-L47)) if `check^H(rt, I₀, a₀, pf₀) = check^H(rt, I₁, a₁, pf₁) = 1` and `a₀[i] ≠ a₁[i]` for some `i ∈ I₀ ∩ I₁` ([Lean](CommitGolf/Binding.lean#L28-L31)). Only `A`'s calls count.

`Certificate` proves all five statements directly. `HidingCertificate` extends it with
[statement 6, hiding](CommitGolf/Statements.lean#L54-L64). Track names add only the oracle-model
restriction; the comparator selects the complete named certificate for the chosen track.

## Hiding specification

[Statement 6](CommitGolf/Statements.lean#L54-L64) uses two-message statistical hiding for
commitments and one opening, corresponding to the privacy goal of CY24, Lemma 18.6.3.
The adversary chooses two messages `m₀, m₁`, a set `I` of `q` positions, and retained state.
Its choices must satisfy `m₀[I] = m₁[I]`; outside `I` they may agree or differ arbitrarily.
Each experiment honestly commits to one of those messages, opens `I`, and lets the adversary
observe the commitment and proof. The total variation distance between its output distributions
must be at most `HIDING_ERROR(q, t)` for every such adversary using at most `t` public queries
across both stages. Empty openings are included. Honest commit/open queries do not consume
that adversary budget. Oracle state persists across all phases within each experiment.

There is no solver-supplied simulator or PPT environment. This is an indistinguishability
requirement, not a runtime certificate: the honest budgets count oracle calls, not local work.
A canonical simulator can fill unopened positions with zeros and honestly commit/open;
its efficiency would additionally require efficient honest algorithms and padding.
The connection to the earlier simulation definition has not been formalized here.

The named certificates in `Statements.lean` expose four oracle tracks, each with a non-hiding
and hiding variant: `IdealPermutationCertificate`, `IdealCompressionCertificate`,
`RandomOracleFixedOutputCertificate`, `IdealXofCertificate`, and their corresponding
`…HidingCertificate` names. Each is a complete requirement. Import `CommitGolf.Statements`
(also exported by `CommitGolf`). The hiding variants fix the provisional target in
`Parameters.lean`: `HIDING_ERROR(q, t) = min(1, (t + 1) / 2^HIDING_SECURITY_BITS)`,
with 128 bits, uniformly in `q`. This policy awaits review; no hiding construction is certified yet.
The verifier selects the hiding certificates for the four `-hiding` track IDs, each using its
own `submissions/<track>/` path, and never falls back to non-hiding checks.

## Submission

Select `submissions/ideal-permutation/`, `submissions/ideal-compression/`, `submissions/random-oracle-fixed-output/`, or `submissions/ideal-xof/`, or append `-hiding` to any of those track names. Each directory holds `claim.json`,
with `proofBytes` and `checkCalls`, and `Solution.lean`, with optional modules under
`CommitGolfCandidate/`. `Solution.lean` defines `CommitGolf.Challenge.submission : Scheme` and
proves `CommitGolf.Challenge.certificate` with the selected named certificate applied to
`submission proofBytes checkCalls`. Non-hiding certificates require statements 1–5; hiding
certificates additionally require statement 6. Both restrict the declared oracle model.
The trusted verifier selects the certificate; the submission cannot override it.
Allowed imports are `CommitGolf`, `CommitGolfBaseline`, and the pinned dependencies (Lean,
Batteries, Mathlib, VCVio). Permutation and compression have certified baseline examples; fixed-output RO, XOF, and hiding starters are pending.

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
