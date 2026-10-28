import CommitGolf.Parameters
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.QueryTracking.WriterCost
import VCVio.OracleComp.Constructions.SampleableType

/-! # Shared ideal oracles

Every party has access to the same 512→256 compression function and 256-bit permutation.
Public queries select compression, forward permutation, or inverse permutation. Each costs
one call, including repeats. Private coins and local computation are free in this query model.

`OracleComp spec α` describes a computation using `spec`; `A →ₒ B` specifies an oracle from
`A` to `B`. The sum `spec₁ + spec₂` provides both, tagged `.inl` and `.inr`. `unifSpec` supplies
private coins, and `ProbComp` is a computation over those coins. `$ᵗ T` samples uniformly from
finite `T`. Sampling whole functions below defines the security experiment mathematically;
it is not an instruction to materialize their truth tables in an implementation.
-/

namespace CommitGolf
open OracleComp OracleSpec

abbrev Compression := BitVec 512 → BitVec 256
abbrev Perm := Equiv.Perm (BitVec 256)
abbrev CompressionSpec := BitVec 512 →ₒ BitVec 256
abbrev PermSpec := (BitVec 256 →ₒ BitVec 256) + (BitVec 256 →ₒ BitVec 256)

/-- `.inl x` compresses; `.inr (.inl x)` permutes; `.inr (.inr y)` inverts. -/
abbrev PublicSpec := CompressionSpec + PermSpec

/-- Commitment, opening, and adversaries may use coins; verification uses `PublicSpec`. -/
abbrev World := unifSpec + PublicSpec

/-- One realization of the two functions, shared by all parties. -/
structure Oracle where
  compression : Compression
  permutation : Perm

namespace Oracle

/-- Independent uniform sampling of the two primitives, once per experiment. -/
def sample : ProbComp Oracle := do
  let compression ← $ᵗ Compression
  let permutation ← $ᵗ Perm
  return ⟨compression, permutation⟩

def answer (oracle : Oracle) {m : Type → Type} [Monad m] : QueryImpl PublicSpec m
  | .inl x => pure (oracle.compression x)
  | .inr (.inl x) => pure (oracle.permutation x)
  | .inr (.inr y) => pure (oracle.permutation.symm y)

/-- Forward private coins; answer all public queries with the fixed functions. -/
def world (oracle : Oracle) : QueryImpl World ProbComp :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) + oracle.answer (m := ProbComp)

def callCost : World.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

/-- Probabilistic execution with its public query count. -/
def run (oracle : Oracle) {α : Type} (computation : OracleComp World α) : ProbComp (α × Nat) :=
  (simulateQ (oracle.world.withAddCost callCost) computation).run

/-- Deterministic execution with its public query count. -/
def eval (oracle : Oracle) {α : Type} (computation : OracleComp PublicSpec α) : α × Nat :=
  (simulateQ ((oracle.answer (m := Id)).withAddCost fun _ => 1) computation).run

end Oracle
end CommitGolf
