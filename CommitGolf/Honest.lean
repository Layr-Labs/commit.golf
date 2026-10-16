import CommitGolf.Scheme

/-! # Honest run

Commit to a message, open a set of positions, check the opening, and record each stage's calls.
Completeness, the budgets, and both scores are statements about this run. -/

namespace CommitGolf
open OracleComp OracleSpec

namespace Scheme
variable (scheme : Scheme)

structure HonestResult where
  /-- Whether `check` accepted. -/
  accepted : Bool
  commitCalls : Nat
  openCalls : Nat
  /-- The second score. -/
  checkCalls : Nat
  /-- The length of `pf` in bytes: the first score. -/
  proofBytes : Nat

/-- `(rt, td) ← commit m`, then `pf ← opening td I`, then `check rt I m[I] pf`, against `π`. -/
def honest (π : Perm) (message : Message) (positions : Positions) : ProbComp HonestResult := do
  let ((rt, td), commitCalls) ← π.run (scheme.commit message)
  let (pf, openCalls) ← π.run (scheme.opening td positions)
  let (accepted, checkCalls) := π.eval (scheme.check rt positions (message.restrict positions) pf)
  return { accepted, commitCalls, openCalls, checkCalls, proofBytes := pf.length }

end Scheme

end CommitGolf
