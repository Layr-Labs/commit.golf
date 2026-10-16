# commit.golf · rules

Design a **vector commitment scheme** on top of a random permutation. Schemes are ranked by two worst-case scores, measured when opening 100 positions:

- **proof size**: bytes in the opening proof;
- **verification cost**: permutation calls made by the verifier.

The leaderboard is the Pareto frontier of these two scores, lower being better in both. Every scheme proves in Lean that it is complete and binding, in the sense of Chapter 18 of [CY24] (Chiesa and Yogev, *[Building Cryptographic Proofs from Hash Functions](https://github.com/hash-based-snargs-book/hash-based-snargs-book)*), which states them for Merkle trees: completeness is Lemma 18.2.1 and position binding is Lemma 18.4.1.

## Submission

A submission is the directory `submission/`; the [example](submission/Solution.lean) submits the [baseline](#lean-and-verification).

- `claim.json`: the claimed scores `proofBytes` and `checkCalls`.
- `Solution.lean`, with optional modules under `CommitGolfCandidate/`. It defines the scheme `CommitGolf.Challenge.submission`, three algorithms `commit`, `opening`, and `check` ([Lean](CommitGolf/Scheme.lean#L23-L38)), and proves `CommitGolf.Challenge.certificate`: [`Certificate submission proofBytes checkCalls`](CommitGolf/Statements.lean#L71-L78), the [five statements](#statements) below.

A submission enters the leaderboard unless an existing entry is at least as good on both scores.

## Parameters

([Lean](CommitGolf/Parameters.lean))

| Constant          | Value                                   |
| ----------------- | --------------------------------------- |
| `WIDTH`           | 1600 bits (a permutation state)         |
| `LENGTH` (`ℓ`)    | 2^24 entries                            |
| `DIGEST_BYTES`    | 32 bytes (an entry, and the commitment) |
| `BATCH`           | 100 positions, opened when scoring      |
| `SECURITY_BITS`   | 128                                     |
| `COMMIT_BUDGET`   | 100 · ℓ calls                           |
| `OPEN_BUDGET(k)`  | 100 · k calls                           |
| `CHECK_BUDGET(k)` | 100 · k calls                           |

A **message** `m` is a vector of `ℓ` entries. A set of **positions** `I` selects some of them, and `m[I]` is the message restricted to `I`. A **proof** is a byte string of any length.

## The permutation

([Lean](CommitGolf/Oracle.lean))

All parties share a permutation `π` of the 1600-bit states. They may evaluate both `π` and its inverse `π⁻¹`; each evaluation is **one call**. Calls are the only cost: local computation is free.

## Scheme

([Lean](CommitGolf/Scheme.lean#L23-L38))

- **`commit(m) → (rt, td)`** commits to the message `m`. It returns a 32-byte commitment `rt` and a trapdoor `td`: any data kept for opening, not scored.
- **`opening(td, I) → pf`** proves the values of `m` at the positions `I`, for any set `I`.
- **`check(rt, I, a, pf) → accept / reject`** decides whether `pf` proves that the committed message has values `a` at the positions `I`. It sees nothing of the message beyond `a`.

`commit` and `opening` may flip coins. `check` may not: its answer depends only on its inputs and `π`.

## Statements

A certificate proves five statements ([Lean](CommitGolf/Statements.lean#L71-L78)). They differ in how `π` is chosen.

The **honest run** ([Lean](CommitGolf/Honest.lean#L27-L37)) on a permutation `π`, a message `m`, and positions `I` computes `(rt, td) ← commit(m)`, then `pf ← opening(td, I)`, then `check(rt, I, m[I], pf)`, counting the calls each algorithm makes.

### Worst case: completeness, budgets, and scores

These hold for **every** `π`, even one chosen to make the scheme fail, for every `m`, and for all coins.

1. **Completeness** ([Lean](CommitGolf/Statements.lean#L18-L25)): for every `I`, `check` accepts in the honest run.
2. **Honest budgets** ([Lean](CommitGolf/Statements.lean#L27-L36)): for every `I`, `commit` makes at most `COMMIT_BUDGET` calls, `opening` at most `OPEN_BUDGET(|I|)`, and `check` at most `CHECK_BUDGET(|I|)` on the honest opening. `check` is not budgeted on other inputs.
3. **Proof size** ([Lean](CommitGolf/Statements.lean#L38-L42)): for every `I` of exactly `BATCH` positions, `pf` has at most `proofBytes` bytes.
4. **Verification cost** ([Lean](CommitGolf/Statements.lean#L44-L49)): for every `I` of exactly `BATCH` positions, `check` makes at most `checkCalls` calls on the honest opening.

### Against an adversary: binding

The **binding game** ([Lean](CommitGolf/Binding.lean#L60-L66)) draws a uniformly random `π`. The adversary ([Lean](CommitGolf/Binding.lean#L40-L47)), who has unlimited computation and may call `π` and `π⁻¹`, outputs a commitment and two openings of it, `(rt, I₀, a₀, pf₀, I₁, a₁, pf₁)` ([Lean](CommitGolf/Binding.lean#L29-L38)). It **wins** ([Lean](CommitGolf/Binding.lean#L54-L58)) if `check` accepts both openings and they **conflict** ([Lean](CommitGolf/Binding.lean#L49-L52)): some position in both `I₀` and `I₁` has different values in `a₀` and `a₁`.

5. **Binding** ([Lean](CommitGolf/Statements.lean#L51-L67)): for every adversary and every `q ≥ 1`, `Pr[the adversary wins and makes at most q calls] ≤ q / 2^128`.

Only the adversary's own calls count, as in [CY24]; the calls `check` makes on its output do not. An adversary making no calls is covered by `q = 1`.

Equivalently: let `ε(q)` be the best winning probability of an adversary that always makes at most `q` calls. The scheme qualifies when `q / ε(q) ≥ 2^128` for every `q` from 1 to `2^128` (the average-case security level of [CY24, §19.2]). A birthday collision on `n`-bit digests already wins with `ε(q) ≈ q² / 2^n`, so `n` must be about 256.

## Lean and verification

The statements are in [`CommitGolf/`](CommitGolf), one file per section above, written with [VCVio](https://github.com/Verified-zkEVM/VCVio). Submissions may import `CommitGolf`, `CommitGolfBaseline`, Mathlib, VCVio, and Lean's standard libraries.

The [verifier](verifier/verify.py), ported from sig.golf, accepts a submission when Lean's [`comparator`](https://github.com/leanprover/comparator), run in a sandbox against the official contract, confirms that:

- the proof passes Lean's kernel, with every declaration replayed (`#print axioms` alone is not enough: it trusts declarations added with kernel checking disabled);
- the theorem is exactly the [challenge](verifier/Challenge.lean.in) for the claimed scores;
- it uses no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.

Build with `lake build CommitGolf CommitGolfBaseline CommitGolfTests`. Verify with `bash scripts/setup.sh` and `python3 scripts/run.py`, on Linux with Landlock and user systemd.

**Baseline.** [`CommitGolfBaseline/Merkle.lean`](CommitGolfBaseline/Merkle.lean) is the textbook binary Merkle tree, compressing with `C(L, R) = trunc₂₅₆ π(0¹⁰⁸⁸ ‖ L ‖ R)`, without path pruning. It scores `(76800 bytes, 2400 calls)`, and [`CommitGolfBaseline/MerkleProof/`](CommitGolfBaseline/MerkleProof) proves its certificate.

## Decisions

Agreed with the organizers:

- the oracle: a random permutation of 1600-bit states, and its inverse;
- `2^24` entries of 32 bytes, and a 32-byte commitment whose size is not scored (this rules out Merkle caps and multi-root commitments);
- worst-case scores, for every `π`, `m`, set of 100 positions, and all coins, ranked on a Pareto frontier;
- worst-case budgets, for every `π`, `m`, `I`, and all coins: `100·ℓ` calls for `commit`, and `100·|I|` for `opening` and for `check` on honest openings;
- binding: `q / ε(q) ≥ 2^128` for every `q` from 1 to `2^128`.

As in [CY24]: perfect completeness, a deterministic `check`, and binding that counts only the adversary's calls.

## Known limitations

- **Binding, not extractability.** SNARGs (Micali, BCS) need the stronger extractability of [CY24, §18.5].
- **No hiding.** Salted, hiding commitments ([CY24, §18.6]) are not required.
- **No preprocessing.** Real permutations are fixed and public, so attackers can precompute; this is not modeled.
- **One commitment.** Attacks on many commitments or users at once are not modeled.
- **Classical adversaries only.**
- **Calls, not cycles.** Every call costs the same; local computation is free.
- **Opened values are free.** Proof size counts `pf` only, not the values `a`.
- **Malformed proofs.** `check` is budgeted on honest openings only, so it may be slow on other inputs.
- **Ideal model only.** A `check` that accepts anything when `π` maps a hard-coded state to a hard-coded Keccak-f output is provably binding for a random `π`, yet broken for Keccak-f. Submissions are reviewed by hand for such backdoors.
- **One permutation width.** Field-native permutations such as Poseidon2 are not modeled.
