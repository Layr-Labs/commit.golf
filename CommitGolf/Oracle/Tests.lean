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

/-! ## Variable-input, fixed-output random oracles -/

private abbrev R : OracleFamily := .randomOracleFixedOutput 2 (by decide)
private abbrev Rs := R.sum R

example : Rs.InTrack .randomOracleFixedOutput := by decide
example : ¬ (R.sum C).InTrack .randomOracleFixedOutput := by decide
example : ¬ (R.sum P).InTrack .idealPermutation := by decide
example : ¬ R.InTrack .idealCompression := by decide
example : ¬ R.HasFiniteDomain := by decide
example : ¬ (C.sum R).HasFiniteDomain := by decide

-- Empty inputs and arbitrary finite lengths are valid; length is part of the input.
example : ([] : R.Domain) ≠ [false] := by decide
example : ([true] : R.Domain) ≠ [true, false] := by decide
example : R.callCost (.inl 3) = 0 := rfl
example : R.callCost (.inr []) = 1 := rfl
example : R.callCost (.inr (List.replicate 10000 false)) = 1 := rfl

-- Fresh inputs receive a uniform answer, recorded in the cache.
example (x : RandomOracleFixedOutput.Input) :
    (R.sharedAnswer x).run ∅ = (do
      let y ← $ᵗ BitVec 2
      return (y, (∅ : RandomOracleFixedOutput.Cache 2).cacheQuery x y)) := by
  simp [OracleFamily.sharedAnswer, RandomOracleFixedOutput.answer, map_eq_bind_pure_comp]

-- Cached answers persist, including between adversary and verifier phases.
example (x : RandomOracleFixedOutput.Input) (y : BitVec 2) :
    (R.sharedAnswer x).run ((∅ : RandomOracleFixedOutput.Cache 2).cacheQuery x y) =
      pure (y, (∅ : RandomOracleFixedOutput.Cache 2).cacheQuery x y) := by
  simp [OracleFamily.sharedAnswer, RandomOracleFixedOutput.answer]

-- Two instances can return different answers to the same input.
example (x : RandomOracleFixedOutput.Input) (y z : BitVec 2) :
    (Rs.sharedAnswer (.inl x)).run
      ((∅ : RandomOracleFixedOutput.Cache 2).cacheQuery x y, (∅ : RandomOracleFixedOutput.Cache 2).cacheQuery x z) =
      pure (y, (∅ : RandomOracleFixedOutput.Cache 2).cacheQuery x y,
        (∅ : RandomOracleFixedOutput.Cache 2).cacheQuery x z) := by
  simp [OracleFamily.sharedAnswer, RandomOracleFixedOutput.answer]

-- Repeats consume two calls but sample just once.
private def randomRepeats (x : RandomOracleFixedOutput.Input) : OracleComp R.world (BitVec 2 × BitVec 2) := do
  let a ← (R.world.query (.inr x) :)
  let b ← (R.world.query (.inr x) :)
  return (a, b)

example (x : RandomOracleFixedOutput.Input) :
    (R.runShared (randomRepeats x)).run ∅ = (do
      let y ← $ᵗ BitVec 2
      return (((y, y), 2), (∅ : RandomOracleFixedOutput.Cache 2).cacheQuery x y)) := by
  simp [OracleFamily.runShared, randomRepeats, OracleFamily.sharedAnswer,
    RandomOracleFixedOutput.answer, OracleFamily.callCost, map_eq_bind_pure_comp]
  change ((do
    let a ← R.sharedAnswer x
    let b ← R.sharedAnswer x
    return ((a, b), 2)) : StateT R.State ProbComp ((BitVec 2 × BitVec 2) × Nat)).run ∅ = _
  simp [OracleFamily.sharedAnswer, RandomOracleFixedOutput.answer, map_eq_bind_pure_comp]

-- Independent instances sample separately even on the identical input.
example (x : RandomOracleFixedOutput.Input) :
    ((do
      let a ← Rs.sharedAnswer (.inl x)
      let b ← Rs.sharedAnswer (.inr x)
      return (a, b)) : StateT Rs.State ProbComp (BitVec 2 × BitVec 2)).run (∅, ∅) = (do
        let a ← $ᵗ BitVec 2
        let b ← $ᵗ BitVec 2
        return ((a, b), (∅ : RandomOracleFixedOutput.Cache 2).cacheQuery x a,
          (∅ : RandomOracleFixedOutput.Cache 2).cacheQuery x b)) := by
  simp [OracleFamily.sharedAnswer, RandomOracleFixedOutput.answer, map_eq_bind_pure_comp]

-- The binding experiment shares the adversary's cache with both verification calls.
private def emptyClaim : Scheme.Claim where
  root := 0
  positions₀ := ∅
  values₀ := fun _ => 0
  proof₀ := []
  positions₁ := ∅
  values₁ := fun _ => 0
  proof₁ := []

-- A small test fixture, not a secure commitment scheme.
private def probeScheme : Scheme where
  oracles := R
  Trapdoor := Unit
  commit _ := pure (0, ())
  opening _ _ := pure []
  check _ _ _ _ := do
    let y ← (R.spec.query [] :)
    return y == 0

private def probeAdversary : Scheme.Adversary R := do
  let _ ← (R.world.query (.inr []) :)
  return emptyClaim

example : probeScheme.bindingGame probeAdversary = (do
    let y ← $ᵗ BitVec 2
    return (emptyClaim, 1, y == 0, y == 0)) := by
  change (do
    let result ← ((do
      let _ ← R.sharedAnswer []
      let a ← R.sharedAnswer []
      let b ← R.sharedAnswer []
      return (emptyClaim, 1, a == 0, b == 0)) :
      StateT R.State ProbComp (Scheme.Claim × Nat × Bool × Bool)).run ∅
    return result.1) = _
  simp [OracleFamily.sharedAnswer, RandomOracleFixedOutput.answer, map_eq_bind_pure_comp]

-- A query first made by verification is sampled too, then reused by the second check.
example : probeScheme.bindingGame (pure emptyClaim) = (do
    let y ← $ᵗ BitVec 2
    return (emptyClaim, 0, y == 0, y == 0)) := by
  change (do
    let result ← ((do
      let a ← R.sharedAnswer []
      let b ← R.sharedAnswer []
      return (emptyClaim, 0, a == 0, b == 0)) :
      StateT R.State ProbComp (Scheme.Claim × Nat × Bool × Bool)).run ∅
    return result.1) = _
  simp [OracleFamily.sharedAnswer, RandomOracleFixedOutput.answer, map_eq_bind_pure_comp]

-- Different inputs in one instance get independent samples.
example : ((do
    let a ← R.sharedAnswer []
    let b ← R.sharedAnswer [false]
    return (a, b)) : StateT R.State ProbComp (BitVec 2 × BitVec 2)).run ∅ = (do
      let a ← $ᵗ BitVec 2
      let b ← $ᵗ BitVec 2
      return ((a, b), ((∅ : RandomOracleFixedOutput.Cache 2).cacheQuery [] a).cacheQuery [false] b)) := by
  simp [OracleFamily.sharedAnswer, RandomOracleFixedOutput.answer, map_eq_bind_pure_comp]

end CommitGolf.OracleTests
