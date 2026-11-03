import CommitGolf.Parameters
import VCVio.OracleComp.Coercions.Add.Basic
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.QueryTracking.WriterCost
import VCVio.OracleComp.Constructions.SampleableType

/-! # Shared ideal oracles

Every party has access to the same 512→256 compression function and 1,600-bit permutation.
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

abbrev Compression := BitVec COMPRESSION_INPUT_LENGTH → BitVec COMPRESSION_OUTPUT_LENGTH
abbrev Perm := Equiv.Perm (BitVec PERMUTATION_WIDTH)
abbrev CompressionSpec := BitVec COMPRESSION_INPUT_LENGTH →ₒ BitVec COMPRESSION_OUTPUT_LENGTH
abbrev PermSpec :=
  (BitVec PERMUTATION_WIDTH →ₒ BitVec PERMUTATION_WIDTH) +
  (BitVec PERMUTATION_WIDTH →ₒ BitVec PERMUTATION_WIDTH)

/-- `.inl x` compresses; `.inr (.inl x)` permutes; `.inr (.inr y)` inverts. -/
abbrev PublicSpec := CompressionSpec + PermSpec

/-- Commitment, opening, and adversaries may use coins; verification uses `PublicSpec`. -/
abbrev World := unifSpec + PublicSpec

/-- One realization of the two functions, shared by all parties. -/
structure Oracle where
  compression : Compression
  permutation : Perm

/-- Independent uniform sampling of the two primitives, once per experiment. -/
def Oracle.sample : ProbComp Oracle := do
  let compression ← $ᵗ Compression
  let permutation ← $ᵗ Perm
  return ⟨compression, permutation⟩

def Oracle.answer (oracle : Oracle) {m : Type → Type} [Monad m] : QueryImpl PublicSpec m
  | .inl x => pure (oracle.compression x)
  | .inr (.inl x) => pure (oracle.permutation x)
  | .inr (.inr y) => pure (oracle.permutation.symm y)

/-- Forward private coins; answer all public queries with the fixed functions. -/
def Oracle.world (oracle : Oracle) : QueryImpl World ProbComp :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) + oracle.answer (m := ProbComp)

/-- One unit per compression or permutation call, forward or inverse;
private coins do not count toward the query budget. -/
def Oracle.callCost : World.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

/-- Probabilistic execution with its public query count. -/
def Oracle.run (oracle : Oracle) {α : Type} (computation : OracleComp World α) : ProbComp (α × Nat) :=
  (simulateQ (oracle.world.withAddCost Oracle.callCost) computation).run

/-- Deterministic execution with its public query count. -/
def Oracle.eval (oracle : Oracle) {α : Type} (computation : OracleComp PublicSpec α) : α × Nat :=
  (simulateQ ((oracle.answer (m := Id)).withAddCost fun _ => 1) computation).run

end CommitGolf
