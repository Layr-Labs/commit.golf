import CommitGolf.Statements
import CommitGolf.Oracle.Finite

/-! # Oracle and track regression tests -/
namespace CommitGolf.OracleTests
open OracleComp OracleSpec

private abbrev P : OracleFamily := .permutation 3 (by decide)
private abbrev C : OracleFamily := .compression 4 2 (by decide) (by decide)
private abbrev copies := OracleFamily.sum C C

example : (P.sum P).InTrack .idealPermutation := by decide
example : copies.InTrack .idealCompression := by decide
example : ¬ C.InTrack .idealPermutation := by decide
example : ¬ P.InTrack .idealCompression := by decide
example : ¬ (P.sum C).InTrack .idealPermutation := by decide
example : ¬ (P.sum C).InTrack .idealCompression := by decide

-- The primitive constructors require valid sizes, proved in Lean.
example : ¬ (0 < 0 ∧ 0 < 4) := by decide
example : ¬ (0 < 4 ∧ 4 < 4) := by decide

-- Identical oracle declarations have independent realizations and separate query routing.
private def H : copies.Realization := (fun _ => 1, fun _ => 2)
private def distinguish : OracleComp copies.spec (BitVec 2 × BitVec 2) := do
  let a ← (copies.spec.query (.inl 7) :)
  let b ← (copies.spec.query (.inr 7) :)
  return (a, b)
#guard copies.eval H distinguish == ((1, 2), 2)

private def repeats : OracleComp C.spec (BitVec 2 × BitVec 2) := do
  let a ← (C.spec.query 7 :)
  let b ← (C.spec.query 7 :)
  return (a, b)
#guard C.eval (fun x => x.setWidth 2) repeats == ((3, 3), 2)

-- Inverse queries use the same permutation and cost a call too.
private def roundtrip : OracleComp P.spec (BitVec 3) := do
  let y ← (P.spec.query (.inl 5) :)
  (P.spec.query (.inr y) :)
#guard P.eval (Equiv.swap 5 7) roundtrip == (5, 2)

-- A coin is free; every instance's queries are charged.
example : copies.callCost (.inl 3) = 0 := rfl
example : copies.callCost (.inr (.inl 7)) = 1 := rfl
example : copies.callCost (.inr (.inr 7)) = 1 := rfl

-- Sampling a family is the product of independent instance samples.
example : copies.sample = (do return (← C.sample, ← C.sample)) := rfl

end CommitGolf.OracleTests
