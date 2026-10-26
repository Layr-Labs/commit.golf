import CommitGolf.Oracle

/-! # Scheme

A vector commitment scheme, with the syntax of [CY24, §18.1]. -/

namespace CommitGolf
open OracleComp OracleSpec

/-- A vector commitment scheme.

- `commit m` returns a commitment `rt` and an opening trapdoor `td`, any data kept for `opening`.
- `opening td I` returns a proof `pf` for the positions `I`.
- `check rt I a pf` decides whether `pf` proves that the committed vector has values `a` at `I`.

`commit` and `opening` may flip coins; `check` may not. All three may query the declared family. -/
structure Scheme where
  /-- Public, fixed oracle declaration; the track certificate restricts its primitive types. -/
  oracles : OracleFamily := OracleFamily.baseline
  Trapdoor : Type
  commit : Message → OracleComp oracles.world (Commitment × Trapdoor)
  opening : Trapdoor → (positions : Positions) → OracleComp oracles.world Proof
  check : Commitment → (positions : Positions) → Values positions → Proof →
    OracleComp oracles.spec Bool

end CommitGolf
