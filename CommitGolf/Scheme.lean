import CommitGolf.Oracle

/-! # Scheme

A vector commitment scheme, with the syntax of [CY24, §18.1]. -/

namespace CommitGolf
open OracleComp OracleSpec

/-- A vector commitment scheme.

- `commit m` returns a commitment `rt` and a trapdoor `td`, any data kept for `opening`.
- `opening td I` returns a proof `pf` for the positions `I`.
- `check rt I a pf` decides whether `pf` proves that the committed vector has values `a` at `I`.

`commit` and `opening` may flip coins; `check` may not. All three may call `π` and `π⁻¹`. -/
structure Scheme where
  Trapdoor : Type
  commit : Message → OracleComp World (Commitment × Trapdoor)
  opening : Trapdoor → (positions : Positions) → OracleComp World Proof
  check : Commitment → (positions : Positions) → Values positions → Proof →
    OracleComp PermSpec Bool

end CommitGolf
