# commit.golf · rules

Design a **vector commitment scheme** in the **ideal permutation model** that pushes the Pareto frontier of two scores, both averaged over openings of 100 random positions:

- **proof size**: bytes in the opening proof;
- **verification cost**: permutation calls made by `check`.

Every scheme proves, in Lean, perfect completeness and position binding with error at most `q / 2^128` against adversaries making `q` permutation calls.

The definitions follow Chapter 18 of [CY24] (Chiesa and Yogev, *[Building Cryptographic Proofs from Hash Functions](https://github.com/hash-based-snargs-book/hash-based-snargs-book)*), read for any scheme `VC` instead of the Merkle scheme `MT`.

## Submission

1. A scheme: three algorithms `commit`, `opening`, and `check` ([`Scheme`](CommitGolf/Scheme.lean#L23-L38)).
2. Two integers `proofBytes` and `checkCalls`: the claimed scores.
3. A Lean proof of [`Certificate scheme proofBytes checkCalls`](CommitGolf/Statements.lean#L70-L77), that is, of the [five statements](#statements) below.

The leaderboard is the Pareto frontier of `(proofBytes, checkCalls)`, lower being better in both. A submission enters it unless an existing entry is at least as good on both scores.

## Parameters

([Lean](CommitGolf/Parameters.lean))

| Constant          | Value                                     |
| ----------------- | ----------------------------------------- |
| `WIDTH`           | 1600 bits, the state of the permutation   |
| `DIGEST_BYTES`    | 32 bytes                                  |
| `LENGTH` (`ℓ`)    | 2^24 entries                              |
| `BATCH`           | 100 positions                             |
| `SECURITY_BITS`   | 128                                       |
| `COMMIT_BUDGET`   | 100 · ℓ permutation calls                 |
| `OPEN_BUDGET(k)`  | 100 · k permutation calls                 |

| Object                   | Content                                                    |
| ------------------------ | ---------------------------------------------------------- |
| State                    | 1600 bits                                                  |
| Entry                    | 32 bytes                                                   |
| Commitment `rt`          | 32 bytes                                                   |
| Message `m`              | one entry at each of the `ℓ` positions                     |
| Positions `I`            | a set of positions                                         |
| Values `a`               | one entry at each position of `I`, and nothing else        |
| Proof `pf`               | a byte string of any length                                |

`m[I]` is the message restricted to the positions in `I`.

## Permutation oracle

([Lean](CommitGolf/Oracle.lean))

Everyone shares one permutation `π` of the 1600-bit states. Everyone may query `π` (forward) and `π⁻¹` (inverse); each query of either kind is **one call**. Only calls are budgeted and scored; local computation is free.

- Statements that hold *for every* permutation run the algorithms against a fixed `π`.
- The scores and binding draw `π` uniformly from all permutations.

## Scheme

([Lean](CommitGolf/Scheme.lean#L23-L38))

- **`commit(m) → (rt, td)`** commits to a message. It may flip coins and call `π`/`π⁻¹`. The trapdoor `td` is any data the scheme likes; it is not scored.
- **`opening(td, I) → pf`** opens any set of positions `I`. It may flip coins and call `π`/`π⁻¹`.
- **`check(rt, I, a, pf) → accept / reject`** decides whether `pf` proves that the committed message has values `a` at positions `I`. It may call `π`/`π⁻¹` but flips no coins.

## Honest experiment

([Lean](CommitGolf/Honest.lean#L30-L40)) For a permutation `π`, a message `m` and positions `I`:

1. `(rt, td) ← commit(m)`
2. `pf ← opening(td, I)`
3. `b ← check(rt, I, m[I], pf)`

It records whether `check` accepted, the calls of each algorithm, and the length of `pf` in bytes.

The **scored run** ([Lean](CommitGolf/Honest.lean#L55-L60)) draws a uniform `π` and a uniform set `I` of exactly `BATCH` distinct positions ([Lean](CommitGolf/Honest.lean#L48-L53)), then runs the honest experiment once.

## Binding game

([Lean](CommitGolf/Binding.lean#L59-L65))

1. Draw a uniform `π`.
2. The adversary, with access to `π` and `π⁻¹`, outputs a commitment and two openings of it: `(rt, I₀, a₀, pf₀, I₁, a₁, pf₁)` ([Lean](CommitGolf/Binding.lean#L28-L37)).
3. It **wins** ([Lean](CommitGolf/Binding.lean#L53-L57)) if `check(rt, I₀, a₀, pf₀)` and `check(rt, I₁, a₁, pf₁)` both accept and the openings **conflict** ([Lean](CommitGolf/Binding.lean#L48-L51)): some position in both `I₀` and `I₁` has different values in `a₀` and `a₁`.

The adversary has unlimited computation and private coins ([Lean](CommitGolf/Binding.lean#L39-L46)). Only its own calls are counted, not those `check` makes on its output.

## Statements

A certificate proves these five statements ([Lean](CommitGolf/Statements.lean#L70-L77)).

1. **Completeness** ([Lean](CommitGolf/Statements.lean#L17-L24)): for every `π`, `m`, `I` and all coins, `check` accepts in the honest experiment.
2. **Honest budgets** ([Lean](CommitGolf/Statements.lean#L26-L32)): for every `π`, `m`, `I` and all coins, `commit` makes at most `COMMIT_BUDGET` calls and `opening` at most `OPEN_BUDGET(|I|)`.
3. **Proof size** ([Lean](CommitGolf/Statements.lean#L34-L40)): for every `m`, the expected length of `pf` in the scored run is at most `proofBytes`.
4. **Verification cost** ([Lean](CommitGolf/Statements.lean#L42-L48)): for every `m`, the expected number of calls made by `check` in the scored run is at most `checkCalls`.
5. **Binding** ([Lean](CommitGolf/Statements.lean#L50-L66)): for every adversary and every `q ≥ 1`, `Pr[the adversary wins and makes at most q calls] ≤ q / 2^128`.

Expectations are over `π`, `I`, and the scheme's coins; the message is worst-case.

For binding, an adversary that makes no calls is covered by `q = 1`. Equivalently, a scheme with binding error `ε(q)` qualifies when `q / ε(q) ≥ 2^128` for every `q` in `[1, 2^128]`; above `2^128` the bound exceeds 1. A birthday collision on `n`-bit digests breaks this unless `n ≳ 256`.

## Lean

The statements live in [`CommitGolf/`](CommitGolf), one file per section above, and use [VCVio](https://github.com/Verified-zkEVM/VCVio). The certificate must pass Lean's kernel, with no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`. Build with `lake build CommitGolf CommitGolfBaseline CommitGolfTests`.

**Baseline.** [`CommitGolfBaseline/Merkle.lean`](CommitGolfBaseline/Merkle.lean) is the textbook binary Merkle tree, with compression `C(L, R) = trunc₂₅₆ π(0¹⁰⁸⁸ ‖ L ‖ R)` and no path pruning. It scores `(76800 bytes, 2400 calls)`, and [`CommitGolfBaseline/MerkleProof/`](CommitGolfBaseline/MerkleProof) proves its certificate.

## Decisions

Agreed with the organizers: a permutation and its inverse as the oracle, 1600-bit width, `2^24` entries of 32 bytes, budgets of `100·ℓ` and `100·|I|` calls, 100 opened positions, a Pareto frontier of the two scores, and the criterion `q / ε(q) ≥ 2^128`.

Proposed in this draft: distinct uniform positions with a worst-case message; only the adversary's calls counted in binding; perfect completeness for every `π`; 32-byte commitments.

## Known limitations

- **Binding, not extractability.** SNARGs (Micali, BCS) need the stronger extractability of [CY24, §18.5].
- **One commitment.** No multi-instance or multi-user attacks are modeled.
- **Classical adversaries only.**
- **Calls, not cycles.** Every call costs the same; local computation is free.
- **Average case.** `check` may be slow on unusual positions or malformed proofs.
- **One permutation width.** Field-native permutations such as Poseidon2 are not modeled.
