import CommitGolf.Parameters
import VCVio.OracleComp.QueryTracking.WriterCost
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.Constructions.SampleableType

/-! # Oracle

The permutation `π` of the states that all parties share. Everyone may query `π` and `π⁻¹`, and
each query of either kind is one *call*: the only cost, local computation being free. Statements
about the honest run hold for every fixed `π`; the binding game draws `π` uniformly from all
permutations.

VCVio vocabulary used here and below. An `OracleComp spec α` is a computation that may query the
oracles in `spec`; `A →ₒ B` specifies one oracle from `A` to `B`, and `spec₁ + spec₂` offers both,
a query being tagged `.inl` or `.inr`. `unifSpec` is the coin oracle (the query `n` returns a
uniform element of `Fin (n + 1)`) and `ProbComp` is `OracleComp unifSpec`. A `QueryImpl spec m`
answers each query of `spec` by a computation in the monad `m`, and `simulateQ impl c` runs `c`
with every query answered by `impl`. `liftM` embeds a computation over fewer oracles into one over
more. `$ᵗ T` draws a uniform element of `T`; `Pr[p | c]` is the probability that `c` returns a
value satisfying `p`. -/

namespace CommitGolf
open OracleComp OracleSpec

/-- Forward queries `.inl x ↦ π x` and inverse queries `.inr y ↦ π⁻¹ y`. -/
abbrev PermSpec : OracleSpec (State ⊕ State) := (State →ₒ State) + (State →ₒ State)

/-- Private coins and the permutation. `commit`, `opening`, and the adversary run over `World`;
`check` runs over `PermSpec` alone, so it flips no coins. -/
abbrev World := unifSpec + PermSpec

abbrev Perm := Equiv.Perm State

namespace Perm

/-- Answer permutation queries with `π` (`π⁻¹` is `π.symm`). -/
def answer (π : Perm) {m : Type → Type} [Monad m] : QueryImpl PermSpec m
  | .inl x => pure (π x)
  | .inr y => pure (π.symm y)

/-- Forward the coins, answer permutation queries with `π`. -/
def world (π : Perm) : QueryImpl World ProbComp :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) + π.answer (m := ProbComp)

/-- One unit per permutation call, forward or inverse; coins are free. -/
def callCost : World.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

/-- `world π` with a running total of `callCost`. In proof goals the total may display
multiplicatively (VCVio's `AddWriterT` writes to `Multiplicative Nat`). -/
def counted (π : Perm) : QueryImpl World (AddWriterT Nat ProbComp) :=
  π.world.withAddCost callCost

/-- Run a probabilistic computation against `π`: its result and its number of calls. -/
def run (π : Perm) {α : Type} (c : OracleComp World α) : ProbComp (α × Nat) :=
  (simulateQ π.counted c).run

/-- Run a coin-free computation, such as `check`, against `π`: its result and its number of
calls. -/
def eval (π : Perm) {α : Type} (c : OracleComp PermSpec α) : α × Nat :=
  (simulateQ ((π.answer (m := Id)).withAddCost fun _ => 1) c).run

end Perm

end CommitGolf
