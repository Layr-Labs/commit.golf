import CommitGolf.Scheme

/-! # Honest experiment

The honest run that completeness, the budgets, and both scores talk about: commit to a message,
open a set of positions, check the opening. Every stage's permutation calls are counted separately.

Scores are averaged over the *scored run*: a uniform permutation and a uniform set of exactly
`BATCH` distinct positions, with the message chosen worst-case. -/

namespace CommitGolf
open OracleComp OracleSpec

namespace Scheme
variable (scheme : Scheme)

/-- Everything one honest run produced. -/
structure HonestResult where
  /-- Did `check` accept the honest opening? -/
  accepted : Bool
  /-- Permutation calls made by `commit`. -/
  commitCalls : Nat
  /-- Permutation calls made by `opening`. -/
  openCalls : Nat
  /-- Permutation calls made by `check`. Scored on average. -/
  checkCalls : Nat
  /-- Length of the opening proof in bytes. Scored on average. -/
  proofBytes : Nat

/-- The honest run, for a fixed permutation `π`, message `m`, and positions `I`:
1. `(rt, td) ← commit m`
2. `pf ← opening td I`
3. `b := check rt I m[I] pf`

`commit` and `opening` may flip coins, so this is a probabilistic computation (`ProbComp`). -/
def honest (π : Perm) (message : Message) (positions : Positions) : ProbComp HonestResult := do
  let ((rt, td), commitCalls) ← π.run (scheme.commit message)
  let (pf, openCalls) ← π.run (scheme.opening td positions)
  let (accepted, checkCalls) := π.eval (scheme.check rt positions (message.restrict positions) pf)
  return { accepted, commitCalls, openCalls, checkCalls, proofBytes := pf.length }

/-! ### The scored distribution -/

/-- There are at least `BATCH` positions, so `BATCH` distinct ones can be chosen. -/
instance : Nonempty (Fin BATCH ↪ Index) :=
  ⟨Fin.castLEEmb (by simp [BATCH, LENGTH, LOG_LENGTH])⟩

/-- A uniformly random set of exactly `BATCH` distinct positions. It is the image of a uniform
injection `Fin BATCH ↪ Index`; every set of `BATCH` positions is the image of the same number
(`BATCH!`) of injections, so the image is uniform among those sets. -/
def randomBatch : ProbComp Positions := do
  let embedding ← $ᵗ (Fin BATCH ↪ Index)
  return Finset.univ.map embedding

/-- The scored run for a message `m`: draw a uniform permutation and a uniform batch of `BATCH`
positions, then run the honest experiment once. -/
def scoredRun (message : Message) : ProbComp HonestResult := do
  let π ← $ᵗ Perm
  let positions ← randomBatch
  scheme.honest π message positions

end Scheme

end CommitGolf
