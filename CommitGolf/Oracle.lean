import CommitGolf.Parameters
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.WriterCost

/-! Independent solver-selected random oracles. Cache keys include oracle identity and input.
All participants share one cache per game; private coins remain independent. -/
namespace CommitGolf.VectorCommit
open OracleComp OracleSpec

/-! # Oracle

The random oracle `H` that every program and the adversary share, and its readings: sampled
lazily, so each new input gets an independent uniform answer, with or without a running count of
calls; or fixed to one function, so a statement can hold for every `H`.

VCVio vocabulary used here and below. An `OracleComp spec α` is a computation that may query
the oracles in `spec`; `A →ₒ B` specifies one oracle from `A` to `B`, and `spec₁ + spec₂`
offers both, a query being tagged `.inl` or `.inr`. `unifSpec` is the coin oracle and `ProbComp`
is `OracleComp unifSpec`. A `QueryImpl spec m` answers each query of `spec` by a computation in
the monad `m`; for `m = Id` it is just a function from queries to answers. `simulateQ impl c`
runs `c` with every query answered by `impl`, and `evalWithAnswerFn f c` does so for a plain
function `f`. `liftM` embeds a computation over fewer oracles into one over more. Two notations:
`$ᵗ T` draws a uniform element of `T`; `Pr[p | c]` is the probability that `c` returns a
value satisfying `p`, and `Pr[= x | c]` that it returns exactly `x`. -/

/-- A solver is allowed to supply `count` number of independent oracles each with
their own `inputBits`, `outputBits` constraining the size of the input/output-/
structure OracleFamily where
  count : Nat
  inputBits : Fin count → Nat
  outputBits : Fin count → Nat

/-- A query to a particular oracle in an `OracleFamily` on `input` -/
structure HashQuery (F : OracleFamily) where
  oracle : Fin F.count
  input : BitVec (F.inputBits oracle)
  deriving DecidableEq

/-- An interface for querying a random oracle as a function from -/
abbrev hashSpec (F : OracleFamily) : OracleSpec (HashQuery F) :=
  fun q => BitVec (F.outputBits q.oracle)

/-- The adversary and the honest algorithms have private coins and the same oracles. -/
abbrev World (F : OracleFamily) := unifSpec + hashSpec F

/-- Coin queries forwarded, hash queries lazily cached. The table starts empty. -/
def romImpl (F : OracleFamily) :
    QueryImpl (World F) (StateT (QueryCache (hashSpec F)) ProbComp) :=
  unifFwdImpl (hashSpec F) + (hashSpec F).randomOracle

/-- Run against that lazy family. -/
def withROM {F : OracleFamily} {α : Type}
    (program : OracleComp (World F) α) : ProbComp α :=
  (simulateQ (romImpl F) program).run' ∅

/-- One unit per oracle call, including cache hits; coins are free. -/
def hashCost (F : OracleFamily) : (World F).Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

/-- The same lazy family, with a running total of `hashCost`. -/
def countedOracle (F : OracleFamily) :
    QueryImpl (World F)
      (AddWriterT Nat (StateT (QueryCache (hashSpec F)) ProbComp)) :=
  (romImpl F).withAddCost (hashCost F)

/-- Total hash-cost instrumentation. Counts every hash query of the computation, including cache hits. -/
def withTotalHashCount {F : OracleFamily} {α : Type}
    (program : OracleComp (World F) α) : ProbComp (α × Nat) :=
  (simulateQ (countedOracle F) program).run.run' ∅

/-- Charge only the hash summand, not private coins. -/
def isHashQuery {F : OracleFamily} : (World F).Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance {F : OracleFamily} : DecidablePred (isHashQuery (F := F)) :=
  fun q => match q with
    | .inl _ => isFalse (by simp [isHashQuery])
    | .inr _ => isTrue (by simp [isHashQuery])

end CommitGolf.VectorCommit
