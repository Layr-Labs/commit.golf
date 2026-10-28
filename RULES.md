# commit.golf · rules

Design a hiding vector commitment scheme with the fixed oracle pair below, with the syntax and security notions of Chapter 18 of [CY24] (Chiesa and Yogev, *[Building Cryptographic Proofs from Hash Functions](https://github.com/hash-based-snargs-book/hash-based-snargs-book)*). Schemes are ranked on the Pareto frontier of two scores for openings of 100 positions, lower being better in both:

- **proof size**: bytes in the opening proof;
- **verification cost**: oracle calls made by `check`.

## Model

([Parameters](CommitGolf/Parameters.lean), [Oracle](CommitGolf/Oracle.lean))

| Constant          | Value          |
| ----------------- | -------------- |
| `DIGEST_BYTES`    | 32             |
| `LENGTH` (`ℓ`)    | 2^24           |
| `BATCH`           | 100            |
| `BINDING_SECURITY_BITS` | 120            |
| `HIDING_SECURITY_BITS` | 120            |
| `COMMIT_BUDGET`   | 100 · ℓ calls  |
| `OPEN_BUDGET(k)`  | 100 · k calls  |
| `CHECK_BUDGET(k)` | 100 · k calls  |

Every scheme uses the fixed `PublicSpec` interface: one
512→256-bit ideal compression function and one 1,600-bit ideal permutation. They
are sampled independently. The permutation offers forward and inverse queries.
All parties share the same two instances throughout an experiment.

Solvers may implement derived functions from these primitives. They cannot add
independent instances, change primitive widths, or declare a variable-input RO/XOF.
Every underlying primitive query costs one call, including repeats and inverse
queries. Private coins and local computation remain free in this interim query
accounting. Derived-function calls have no separate unit-cost shortcut.

- A message is `m ∈ Σ^ℓ` with `Σ = {0,1}^256`. For positions `I ⊆ [ℓ] = {0, …, ℓ−1}`, `m[I] ∈ Σ^I` is its restriction.
- A commitment is `rt ∈ {0,1}^256`; a proof `pf` is a byte string of `|pf|` bytes.

## Scheme

([Lean](CommitGolf/Scheme.lean#L10-L24))

- `commit^H(m) → (rt, td)`, probabilistic, where the opening trapdoor `td` has any type;
- `opening^H(td, I) → pf`, probabilistic;
- `check^H(rt, I, a, pf) → {0, 1}` for `a ∈ Σ^I`, deterministic.

The **honest run** ([Lean](CommitGolf/Honest.lean#L23-L28)) on `(H, m, I)` is `(rt, td) ← commit^H(m)`, `pf ← opening^H(td, I)`, `b := check^H(rt, I, m[I], pf)`.

## Statements

The certificate for `(proofBytes, checkCalls)` ([Lean](CommitGolf/Statements.lean#L67)) requires the following five properties plus hiding and the fixed oracle pair. The first four hold in the honest run for every realization `H`, `m`, `I`, and all coins:

1. **Completeness** ([Lean](CommitGolf/Statements.lean#L18-L20)): `b = 1`.
2. **Honest budgets** ([Lean](CommitGolf/Statements.lean#L23-L28)): `commit`, `opening`, and `check` make at most `COMMIT_BUDGET`, `OPEN_BUDGET(|I|)`, and `CHECK_BUDGET(|I|)` calls, respectively.
3. **Proof size** ([Lean](CommitGolf/Statements.lean#L31-L33)): if `|I| = BATCH`, then `|pf| ≤ proofBytes`.
4. **Verification cost** ([Lean](CommitGolf/Statements.lean#L36-L38)): if `|I| = BATCH`, then `check` makes at most `checkCalls` calls.
5. **Binding** ([Lean](CommitGolf/Statements.lean#L41-L44)): for every adversary `A` and every `q ≥ 1`,

   `Pr[A wins and makes at most q calls] ≤ q / 2^BINDING_SECURITY_BITS`.

In the **binding game** ([Lean](CommitGolf/Binding.lean)), the fixed compression function and permutation are sampled independently and uniformly and shared by the adversary and both checks. `A` ([Lean](CommitGolf/Binding.lean#L24-L26)), probabilistic and computationally unbounded, queries the declared collection and outputs `(rt, I₀, a₀, pf₀, I₁, a₁, pf₁)` ([Lean](CommitGolf/Binding.lean#L14-L22)). It **wins** ([Lean](CommitGolf/Statements.lean#L41-L44)) if `check^H(rt, I₀, a₀, pf₀) = check^H(rt, I₁, a₁, pf₁) = 1` and `a₀[i] ≠ a₁[i]` for some `i ∈ I₀ ∩ I₁` ([Lean](CommitGolf/Binding.lean#L28-L31)). Only `A`'s calls count.

`Certificate` requires all six statements, including hiding, and fixes the oracle pair.

## Hiding specification

[Statement 6](CommitGolf/Statements.lean#L51-L61) uses two-message statistical hiding for
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

## Single submission target

`Certificate scheme proofBytes checkCalls` requires all six properties. The scheme
interface fixes the oracle pair, including widths and number of instances; there
is no solver-selected oracle declaration. The hiding target is
`HIDING_ERROR(q, t) = min(1, (t + 1) / 2^HIDING_SECURITY_BITS)`.
The comparator checks this certificate directly; there is no oracle-model selector.

**`submission/` is the only solver-editable directory.** All supporting implementation
and proof modules must live inside it. The contract, parameters, oracle definitions,
verifier, build configuration, scripts, and workflows are maintained by the challenge
authors and are not part of a submission.

Use `submission/`. Define `CommitGolf.Challenge.submission : Scheme`
and prove `CommitGolf.Challenge.certificate : Certificate submission
proofBytes checkCalls`. Supply those two numbers in `claim.json`; optional modules
live under `CommitGolfCandidate/`. The trusted verifier selects the certificate.
There is no certified starter for this target yet.

The table above and the two existing score fields describe what is currently
enforced. Updating to 2,048-bit entries, 128-element openings, and the combined cycle × size score is
pending. RISC-V runtime is not yet part of this certificate.

The [verifier](verifier/verify.py) runs Lean's [`comparator`](https://github.com/leanprover/comparator) in a sandbox. It checks that the proof passes Lean's kernel with every declaration replayed, that it proves exactly the [challenge](verifier/Challenge.lean.in), and that it uses only the axioms `propext`, `Classical.choice`, and `Quot.sound`.

```sh
lake build CommitGolf CommitGolfTests   # build
bash scripts/setup.sh && python3 scripts/run.py # verify (Linux, Landlock, user systemd)
```

## Preserved baselines

The old baseline sources and proofs remain in `CommitGolfBaseline/` for later
adaptation. They are excluded from compilation and verifier imports and are not
current submissions. No new secure starter is supplied by this refactor.
