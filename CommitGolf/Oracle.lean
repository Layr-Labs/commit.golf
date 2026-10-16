import CommitGolf.Parameters
import VCVio.OracleComp.QueryTracking.WriterCost
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.Constructions.SampleableType

/-! # Oracle

The ideal permutation `π` that the scheme and the adversary share.

**The model.** At the start of every experiment, `π` is drawn uniformly from *all* permutations of
the `2 ^ 1600` states. Everybody (`commit`, `opening`, `check`, the adversary) may query `π` in
both directions: forward, `x ↦ π x`, and inverse, `y ↦ π⁻¹ y`. Each query of either kind counts as
one *call*. Calls are the only cost in this competition: local computation is free.

The inverse is offered because practical permutations (Keccak-f, Poseidon2) are efficiently
invertible, so a security proof must not assume otherwise.

**Two ways to use `π` in a statement.**
- Statements that must hold *for every* permutation (completeness, the budgets, and the scores)
  take a fixed `π : Perm` and run the scheme against it.
- Binding is about a *random* permutation: the game samples one with `$ᵗ Perm`.

**VCVio vocabulary.** The statements use the [VCVio](https://github.com/Verified-zkEVM/VCVio)
library for oracle computations. Here is the little of it that the files rely on:

- `OracleComp spec α` is a computation that returns an `α` and may query the oracles in `spec`
  along the way. It is a syntax tree of queries; it means nothing until the queries are answered.
- `A →ₒ B` specifies one oracle taking an `A` and answering a `B`; `spec₁ + spec₂` offers both
  oracles, a query to the first being tagged `.inl` and one to the second `.inr`.
- `unifSpec` is the oracle of private randomness ("coins"): the query `n` returns a uniformly
  random element of `Fin (n + 1)`. `ProbComp α := OracleComp unifSpec α` is a probabilistic
  computation.
- A `QueryImpl spec m` answers each query of `spec` by a computation in the monad `m`;
  `simulateQ impl c` runs `c`, answering every query with `impl`.
- `liftM` embeds a computation over fewer oracles into one over more.
- `$ᵗ T` draws a uniform element of the finite type `T`.
- `Pr[p | c]` is the probability that `c` returns a value satisfying `p`, and `Pr[= x | c]` the
  probability that it returns exactly `x`. -/

namespace CommitGolf
open OracleComp OracleSpec

/-! ### The oracles -/

/-- The permutation as a pair of oracles on `State`:
- `.inl x` asks for `π x` (forward call);
- `.inr y` asks for `π⁻¹ y` (inverse call). -/
abbrev PermSpec : OracleSpec (State ⊕ State) := (State →ₒ State) + (State →ₒ State)

/-- Everything a probabilistic party may query: private coins (`.inl _`) and the permutation
(`.inr _`). `commit`, `opening`, and the adversary run over `World`; `check` runs over `PermSpec`
alone, so it is deterministic once `π` is fixed. -/
abbrev World := unifSpec + PermSpec

/-- One particular permutation of the states. -/
abbrev Perm := Equiv.Perm State

namespace Perm

/-! ### Answering queries with a fixed permutation -/

/-- Answer forward queries with `π` and inverse queries with `π⁻¹` (written `π.symm` in Mathlib). -/
def answer (π : Perm) {m : Type → Type} [Monad m] : QueryImpl PermSpec m
  | .inl x => pure (π x)
  | .inr y => pure (π.symm y)

/-- Answer a `World` query: coins are forwarded unchanged (they stay random), permutation queries
are answered by `π`. -/
def world (π : Perm) : QueryImpl World ProbComp :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) + π.answer (m := ProbComp)

/-! ### Counting calls -/

/-- The cost of a `World` query: one per permutation call, forward or inverse; coins are free. -/
def callCost : World.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

/-- `world π` together with a running count of permutation calls.

`AddWriterT Nat` is VCVio's writer over `Multiplicative Nat`: the count is a sum, but in proof goals
it may appear multiplicatively, so that zero calls displays as `1` and adding counts as `*`. -/
def counted (π : Perm) : QueryImpl World (AddWriterT Nat ProbComp) :=
  π.world.withAddCost callCost

/-- Run a probabilistic computation against `π`. Returns its result and the number of permutation
calls it made; both may depend on the coins. -/
def run (π : Perm) {α : Type} (c : OracleComp World α) : ProbComp (α × Nat) :=
  (simulateQ π.counted c).run

/-- Run a coin-free computation (such as `check`) against `π`. Returns its result and the number
of permutation calls it made; both are determined by `π`. -/
def eval (π : Perm) {α : Type} (c : OracleComp PermSpec α) : α × Nat :=
  (simulateQ ((π.answer (m := Id)).withAddCost fun _ => 1) c).run

end Perm

end CommitGolf
