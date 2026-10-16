import CommitGolf.Scheme

/-! # Honest experiment

The honest run that completeness, the budgets, and both scores talk about: commit to a message,
open a set of positions, check the opening. Every stage's permutation calls are counted separately. -/

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
  /-- Permutation calls made by `check`. The second score. -/
  checkCalls : Nat
  /-- Length of the opening proof in bytes. The first score. -/
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

end Scheme

end CommitGolf
