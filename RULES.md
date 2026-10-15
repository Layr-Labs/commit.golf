# commit.golf · rules

Design a **vector commitment scheme in the ideal permutation model** that pushes the Pareto frontier of two averages, measured when opening `BATCH = 100` random positions:

- **proof size**: bytes in the opening proof;
- **verification cost**: permutation calls made by `check`.

Every scheme must have perfect completeness, and position binding error at most `q / 2^128` against every adversary making `q` permutation calls.

The definitions follow Chapter 18 of [CY24] (Chiesa and Yogev, *[Building Cryptographic Proofs from Hash Functions](https://github.com/hash-based-snargs-book/hash-based-snargs-book)*), read for any scheme `VC` instead of the Merkle scheme `MT`: completeness is Lemma 18.2.1 and position binding is Lemma 18.4.1.

## Submission

1. A Lean term `scheme : CommitGolf.Scheme`: the [three algorithms](#algorithms).
2. Two nonnegative integers `proofBytes` and `checkCalls`: the claimed scores.
3. A Lean proof of [`CommitGolf.Certificate scheme proofBytes checkCalls`](CommitGolf/Statements.lean#L70-L77).

The leaderboard is the Pareto frontier of `(proofBytes, checkCalls)`, lower being better in both. A submission enters it unless an existing entry is at least as good on both scores.

## Parameters

([Lean](CommitGolf/Parameters.lean))

| Constant          |                                    Value |
| ----------------- | ---------------------------------------: |
| `WIDTH`           |        1600 bits (the Keccak-f[1600] state) |
| `DIGEST_BYTES`    |                                 32 bytes |
| `LENGTH` (`ℓ`)    |                      2^24 vector entries |
| `BATCH`           |               100 distinct opened positions |
| `SECURITY_BITS`   |                                      128 |
| `COMMIT_BUDGET`   |                   100·ℓ permutation calls |
| `OPEN_BUDGET(k)`  | 100·k permutation calls for `k` positions |

`check` has no budget: its average cost is the second score.

| Object     | Type                                                   |
| ---------- | ------------------------------------------------------ |
| Entry      | 32 bytes                                               |
| Message    | a vector of `ℓ` entries                                |
| Commitment | 32 bytes                                               |
| Values     | one entry for each position in `I`, and nothing else    |
| Proof      | a byte string of any length; its length is scored      |
| Trapdoor   | any Lean type chosen by the scheme; not scored         |

## Model

### Ideal permutation

([Lean](CommitGolf/Oracle.lean))

The scheme and the adversary share one permutation `π` of `{0,1}^1600`, drawn uniformly from all permutations. Both may query `π` and `π⁻¹`, and each query of either kind counts as **one call**. Local computation is free: only calls are budgeted and scored.

`π⁻¹` is available because practical permutations (Keccak-f, Poseidon2) are efficiently invertible. As a result, plain truncation `trunc(π(L‖R))` is not a collision-resistant compression: inverting two states with equal truncations yields a collision in two calls. Designs need capacity or a feed-forward.

### Algorithms

([Lean](CommitGolf/Scheme.lean#L23-L38))

- **`commit(m) → (rt, td)`** commits to a message `m`. It may use coins and `π`/`π⁻¹`.
- **`opening(td, I) → pf`** opens the positions `I ⊆ [ℓ]`, for any set `I`. It may use coins and `π`/`π⁻¹`.
- **`check(rt, I, a, pf) → bit`** decides whether `pf` authenticates the values `a ∈ Σ^I` at positions `I`. It may use `π`/`π⁻¹` but no coins. It receives only the values at `I`.

## Required Lean statements

### Honest experiment

([Lean](CommitGolf/Honest.lean#L30-L40)) For a permutation `π`, a message `m` and a set of positions `I`:

1. `(rt, td) ← commit(m)`
2. `pf ← opening(td, I)`
3. `b := check(rt, I, m[I], pf)`

The *scored run* ([Lean](CommitGolf/Honest.lean#L55-L60)) draws a uniform `π` and a uniform set `I` of exactly `BATCH` distinct positions, then runs the honest experiment once.

1. **Completeness** ([Lean](CommitGolf/Statements.lean#L17-L24)): for every `π`, `m`, `I` and all coins, `b = 1`. This is perfect completeness, Lemma 18.2.1.
2. **Honest budgets** ([Lean](CommitGolf/Statements.lean#L26-L32)): for every `π`, `m`, `I` and all coins, `commit` makes at most `COMMIT_BUDGET` calls and `opening` at most `OPEN_BUDGET(|I|)`.
3. **Proof size**, the first score ([Lean](CommitGolf/Statements.lean#L34-L40)): for every message `m`, `E[|pf|] ≤ proofBytes`, where `|pf|` is the length in bytes.
4. **Verification cost**, the second score ([Lean](CommitGolf/Statements.lean#L42-L48)): for every message `m`, `E[calls made by check] ≤ checkCalls`.

Both expectations are over the scored run: a uniform `π`, a uniform `I`, and the scheme's coins. The message is worst-case.

### Binding

([Lean](CommitGolf/Binding.lean#L59-L65)) Consider a classical probabilistic adversary `A` with unrestricted computation:

1. Sample `π` uniformly.
2. `A`, with access to `π` and `π⁻¹`, outputs `(rt, I₀, a₀, pf₀, I₁, a₁, pf₁)`.
3. `A` **wins** if some `i ∈ I₀ ∩ I₁` has `a₀[i] ≠ a₁[i]`, `check(rt, I₀, a₀, pf₀) = 1` and `check(rt, I₁, a₁, pf₁) = 1`.

Only `A`'s own calls are counted, as in [CY24]. The calls `check` makes on `A`'s output are not, so a slow `check` cannot make the bound easier to meet. An adversary making no calls is covered by `q = 1`: it must win with probability at most `2^-128`, including by luck in `check`'s own calls.

5. **Binding** ([Lean](CommitGolf/Statements.lean#L50-L66)): for every `A` and every `q ≥ 1`, `Pr[A wins and makes at most q calls] ≤ q / 2^128`.

Equivalently, a construction with binding error `ε(q)` qualifies when `min_{q ∈ [1, 2^128]} q / ε(q) ≥ 2^128`; for `q > 2^128` the bound exceeds 1 and holds trivially. Constructions may prove whatever `ε` they have, typically `O(q² / 2^n)` for `n`-bit digests, and deduce the bound. Because the bound is linear in `q` and must hold up to `q = 2^128`, a birthday collision on `n`-bit values breaks it unless `n ≳ 256`.

## Lean project

[`CommitGolf.Certificate scheme proofBytes checkCalls`](CommitGolf/Statements.lean#L70-L77) is the competition claim. The files under [`CommitGolf/`](CommitGolf) are meant to be read in order:

| File | Contents |
| ---- | -------- |
| [`Parameters`](CommitGolf/Parameters.lean) | constants and object types |
| [`Oracle`](CommitGolf/Oracle.lean) | the permutation oracle and call counting |
| [`Scheme`](CommitGolf/Scheme.lean) | the syntax of a scheme |
| [`Honest`](CommitGolf/Honest.lean) | the honest experiment and the scored run |
| [`Binding`](CommitGolf/Binding.lean) | the binding game |
| [`Statements`](CommitGolf/Statements.lean) | the five statements and the certificate |

Probabilistic computations use [VCVio](https://github.com/Verified-zkEVM/VCVio), pinned in `lake-manifest.json` to the revision sig.golf uses. The certificate must pass Lean's kernel, and its transitive axioms may contain only `propext`, `Classical.choice`, and `Quot.sound`.

Build with `lake build CommitGolf CommitGolfBaseline CommitGolfTests`.

## Baseline

[`CommitGolfBaseline/Merkle.lean`](CommitGolfBaseline/Merkle.lean) defines the binary Merkle tree of [CY24, §18.1], without salts or path pruning, with the compression `C(L, R) = trunc₂₅₆ π(0¹⁰⁸⁸ ‖ L ‖ R)`. It scores `(100 × 24 × 32, 100 × 24) = (76800 bytes, 2400 calls)`. Proving its certificate is the sanity check of these statements.

## Decisions

Agreed with the organizers: an ideal permutation with its inverse as the oracle, 1600-bit width, `ℓ = 2^24` entries of 32 bytes, budgets of `100·ℓ` calls for `commit` and `100·|I|` for `opening`, 100 opened positions, a Pareto frontier of proof size and verification cost, and the binding criterion `min_q q / ε(q) ≥ 2^128`.

Proposed in this draft:

- the opened positions are distinct and uniform, and the message is worst-case;
- the binding game counts only the adversary's calls, as in [CY24], with `q ≥ 1` covering adversaries that make no calls;
- completeness is perfect for every permutation, not merely with high probability over `π`;
- commitments are 32 bytes.

## Known limitations

- **Binding, not extractability.** SNARG constructions (Micali, BCS) use the stronger extractability of [CY24, §18.5]. A scheme can win here without being usable there.
- **Single commitment.** The adversary attacks one commitment in one experiment; no multi-instance or multi-user amortization is modeled.
- **Classical adversaries only.**
- **Calls, not cycles.** Every permutation call costs the same. Local computation, including verifier arithmetic, is free.
- **Average, not worst case.** Both scores average over random positions. `check` may be slow on unusual sets of positions or on malformed proofs.
- **One permutation width.** Field-native permutations such as Poseidon2 over KoalaBear or BabyBear are not modeled.
