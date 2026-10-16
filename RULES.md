# commit.golf · rules

Design a **vector commitment scheme** on top of a random permutation. Schemes are ranked by two averages, measured when opening 100 random positions:

- **proof size**: bytes in the opening proof;
- **verification cost**: permutation calls made by the verifier.

The leaderboard is the Pareto frontier of these two scores, lower being better in both. Every scheme proves in Lean that it is complete and binding.

The definitions are those of Chapter 18 of [CY24] (Chiesa and Yogev, *[Building Cryptographic Proofs from Hash Functions](https://github.com/hash-based-snargs-book/hash-based-snargs-book)*), applied to any scheme rather than just Merkle trees: completeness is Lemma 18.2.1 and position binding is Lemma 18.4.1.

## Submission

1. A scheme: three algorithms `commit`, `opening`, and `check` ([Lean](CommitGolf/Scheme.lean#L23-L38)).
2. Two integers `proofBytes` and `checkCalls`: the claimed scores.
3. A Lean proof of [`Certificate scheme proofBytes checkCalls`](CommitGolf/Statements.lean#L73-L80): the [five statements](#statements) below.

A submission enters the leaderboard unless an existing entry is at least as good on both scores.

## Parameters

([Lean](CommitGolf/Parameters.lean))

| Constant         | Value                         |
| ---------------- | ----------------------------- |
| `WIDTH`          | 1600 bits (a permutation state) |
| `LENGTH` (`ℓ`)   | 2^24 entries                  |
| `DIGEST_BYTES`   | 32 bytes (an entry, and the commitment) |
| `BATCH`          | 100 positions                 |
| `SECURITY_BITS`  | 128                           |
| `COMMIT_BUDGET`  | 100 · ℓ calls                 |
| `OPEN_BUDGET(k)` | 100 · k calls                 |
| `CHECK_BUDGET(k)`| 100 · k calls                 |

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

A certificate proves five statements ([Lean](CommitGolf/Statements.lean#L73-L80)). They differ in how `π` is chosen.

The **honest run** ([Lean](CommitGolf/Honest.lean#L30-L40)) on a permutation `π`, a message `m`, and positions `I` computes `(rt, td) ← commit(m)`, then `pf ← opening(td, I)`, then `check(rt, I, m[I], pf)`, counting the calls each algorithm makes.

### For every permutation

These hold for **every** `π`, even one chosen to make the scheme fail, and for every `m`, every `I`, and all coins.

1. **Completeness** ([Lean](CommitGolf/Statements.lean#L17-L24)): `check` accepts in the honest run.
2. **Honest budgets** ([Lean](CommitGolf/Statements.lean#L26-L35)): `commit` makes at most `COMMIT_BUDGET` calls, `opening` at most `OPEN_BUDGET(|I|)`, and `check` at most `CHECK_BUDGET(|I|)` on the honest opening. `check` is not budgeted on other inputs.

### On average: the scores

The **scored run** ([Lean](CommitGolf/Honest.lean#L55-L60)) draws a uniformly random `π` and a uniformly random set `I` of exactly `BATCH` distinct positions ([Lean](CommitGolf/Honest.lean#L48-L53)), then performs the honest run. For every message `m`:

3. **Proof size** ([Lean](CommitGolf/Statements.lean#L37-L43)): the expected length of `pf` in bytes is at most `proofBytes`.
4. **Verification cost** ([Lean](CommitGolf/Statements.lean#L45-L51)): the expected number of calls made by `check` is at most `checkCalls`.

### Against an adversary: binding

The **binding game** ([Lean](CommitGolf/Binding.lean#L59-L65)) draws a uniformly random `π`. The adversary ([Lean](CommitGolf/Binding.lean#L39-L46)), who has unlimited computation and may call `π` and `π⁻¹`, outputs a commitment and two openings of it, `(rt, I₀, a₀, pf₀, I₁, a₁, pf₁)` ([Lean](CommitGolf/Binding.lean#L28-L37)). It **wins** ([Lean](CommitGolf/Binding.lean#L53-L57)) if `check` accepts both openings and they **conflict** ([Lean](CommitGolf/Binding.lean#L48-L51)): some position in both `I₀` and `I₁` has different values in `a₀` and `a₁`.

5. **Binding** ([Lean](CommitGolf/Statements.lean#L53-L69)): for every adversary and every `q ≥ 1`, `Pr[the adversary wins and makes at most q calls] ≤ q / 2^128`.

Only the adversary's own calls count, as in [CY24]; the calls `check` makes on its output do not. An adversary making no calls is covered by `q = 1`.

Equivalently: let `ε(q)` be the best winning probability of an adversary that always makes at most `q` calls. The scheme qualifies when `q / ε(q) ≥ 2^128` for every `q` from 1 to `2^128` (the average-case security level of [CY24, §19.2]). A birthday collision on `n`-bit digests already wins with `ε(q) ≈ q² / 2^n`, so `n` must be about 256.

## Lean

The statements are in [`CommitGolf/`](CommitGolf), one file per section above, written with [VCVio](https://github.com/Verified-zkEVM/VCVio). A certificate must pass Lean's kernel and use no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`. Build with `lake build CommitGolf CommitGolfBaseline CommitGolfTests`.

**Verification.** A submission is the directory `submission/`: `claim.json` with `proofBytes` and `checkCalls`, `Solution.lean`, and optional modules under `CommitGolfCandidate/`. `Solution.lean` defines `CommitGolf.Challenge.submission` and proves `CommitGolf.Challenge.certificate`; the [example](submission/Solution.lean) submits the baseline. Submissions may import `CommitGolf`, `CommitGolfBaseline`, Mathlib, VCVio and Lean's standard libraries. The [verifier](verifier/verify.py), ported from sig.golf, copies the official contract into a fresh project, writes the [challenge](verifier/Challenge.lean.in) from the claimed scores, and runs Lean's [`comparator`](https://github.com/leanprover/comparator) in a sandbox. `comparator` replays every declaration through the kernel, so a proof that skipped kernel checking is rejected even though `#print axioms` looks clean; it then checks that the statement is the challenge's and that only the three axioms are used. Run it with `bash scripts/setup.sh` and `python3 scripts/run.py` on Linux with Landlock and user systemd.

**Baseline.** [`CommitGolfBaseline/Merkle.lean`](CommitGolfBaseline/Merkle.lean) is the textbook binary Merkle tree, compressing with `C(L, R) = trunc₂₅₆ π(0¹⁰⁸⁸ ‖ L ‖ R)`, without path pruning. It scores `(76800 bytes, 2400 calls)`, and [`CommitGolfBaseline/MerkleProof/`](CommitGolfBaseline/MerkleProof) proves its certificate.

## Decisions

- **Agreed with the organizers:** a random permutation with its inverse as the oracle, 1600-bit width, `2^24` entries of 32 bytes, a 32-byte commitment whose size is not scored (this rules out Merkle caps and multi-root commitments), budgets of `100·ℓ` and `100·|I|` calls, 100 opened positions, a Pareto frontier of the two scores, the criterion `q / ε(q) ≥ 2^128` for every `q` from 1 to `2^128`, and distinct uniform positions.
- **As in [CY24]:** perfect completeness, a deterministic `check`, and binding that counts only the adversary's calls.
- **Proposed in this draft, open for discussion:** budgets counted per entry and in the worst case, a `check` budget of `100·|I|` calls on honest openings only, and a worst-case message.

## Known limitations

- **Binding, not extractability.** SNARGs (Micali, BCS) need the stronger extractability of [CY24, §18.5].
- **No hiding.** Salted, hiding commitments ([CY24, §18.6]) are not required.
- **No preprocessing.** Real permutations are fixed and public, so attackers can precompute; this is not modeled.
- **One commitment.** Attacks on many commitments or users at once are not modeled.
- **Classical adversaries only.**
- **Calls, not cycles.** Every call costs the same; local computation is free.
- **Average case.** Positions and the message do not depend on `π` or on the commitment, unlike in Fiat–Shamir-based SNARGs; `check` may be slow on unusual inputs.
- **One permutation width.** Field-native permutations such as Poseidon2 are not modeled.
