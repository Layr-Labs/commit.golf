import CommitGolf.Oracle

/-! # Scheme

What a submission is: a vector commitment scheme `VC = (VC.Commit, VC.Open, VC.Check)` with the
syntax of [CY24, §18.1], given oracle access to the ideal permutation of `Oracle`.

The three algorithms, informally:

```
commit(m)         → (rt, td)   commit to the vector m; td is kept to produce openings later
opening(td, I)    → pf         prove the values of m at the positions in I
check(rt, I, a, pf) → bit      accept or reject the claim "m[I] = a"
```

`commit` and `opening` are run by the committer: they may flip coins and may call `π` and `π⁻¹`.
`check` is run by the verifier: it may call `π` and `π⁻¹` but flips no coins, so its verdict is a
function of its inputs and of `π`. -/

namespace CommitGolf
open OracleComp OracleSpec

/-- A vector commitment scheme.

- `Trapdoor` is any Lean type the scheme likes: what `commit` hands to `opening`, for instance the
  whole Merkle tree. It is neither scored nor size-limited.
- `commit m` returns a commitment `rt` and a trapdoor `td`. It may use coins and `π`/`π⁻¹`.
- `opening td I` returns an opening proof `pf` for the positions `I`. It may use coins and
  `π`/`π⁻¹`. It must work for every set `I` (completeness), but only `|I| = BATCH` is scored.
- `check rt I a pf` decides whether `pf` proves that the committed vector has values `a` at the
  positions `I`. It may use `π`/`π⁻¹` but no coins (it runs over `PermSpec`, not `World`). It
  sees only the claimed values at `I`, never the rest of the message. -/
structure Scheme where
  Trapdoor : Type
  commit : Message → OracleComp World (Commitment × Trapdoor)
  opening : Trapdoor → (positions : Positions) → OracleComp World Proof
  check : Commitment → (positions : Positions) → Values positions → Proof →
    OracleComp PermSpec Bool

end CommitGolf
