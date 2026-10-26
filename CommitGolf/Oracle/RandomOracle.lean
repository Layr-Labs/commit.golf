import CommitGolf.Oracle.IdealCompression
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic

/-! # Variable-input, fixed-output random oracle

Inputs are finite bit strings, including the empty string. Each instance fixes a positive
output width. Fresh inputs receive independent uniform answers; repeats reuse a cached answer.
There is no bound on input length and each query costs one call. -/
namespace CommitGolf.RandomOracle
open OracleComp OracleSpec

abbrev Input := List Bool
abbrev Spec (outputBits : Nat) : OracleSpec Input := Input →ₒ BitVec outputBits
abbrev Function (outputBits : Nat) := Input → BitVec outputBits
abbrev Cache (outputBits : Nat) := (Spec outputBits).QueryCache

/-- Lazy sampling supports the infinite input domain without sampling a whole function. -/
abbrev answer (outputBits : Nat) : QueryImpl (Spec outputBits)
    (StateT (Cache outputBits) ProbComp) := (Spec outputBits).randomOracle

end CommitGolf.RandomOracle
