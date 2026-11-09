import Mathlib.Data.FinEnum
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Real.Basic

/-! # Parameters

Constants and object types, following [CY24, Chapter 18]. Files, in order: `Parameters`,
`Oracle`, `Scheme`, `Honest`, `Binding`, `Statements`. -/

namespace CommitGolf

/-! ### Sizes -/

/-- Width of the ideal permutation in bits, matching the Keccak-f[1600] state. -/
def PERMUTATION_WIDTH : Nat := 1600

/-- Input length of the ideal compression function, in bits. -/
def COMPRESSION_INPUT_LENGTH : Nat := 512

/-- Output length of the ideal compression function, in bits. -/
def COMPRESSION_OUTPUT_LENGTH : Nat := 256

/-- Bits in each logical vector leaf; independent of the solver’s internal tree layout. -/
def LEAF_SIZE : Nat := 2048

/-- Bytes in a commitment. -/
def DIGEST_BYTES : Nat := 32

def DIGEST_BITS : Nat := 8 * DIGEST_BYTES

def LOG_LENGTH : Nat := 24

/-- Entries in a committed vector, `ℓ = 2 ^ 24`. -/
def LENGTH : Nat := 2 ^ LOG_LENGTH

/-! ### Scoring and security -/

/-- Explicit cost-model assumption: abstract machine cycles charged per compression syscall.
This is a benchmark price, not a measured hardware cycle count. -/
def COMPRESSION_CYCLES : Nat := 8

/-- Explicit cost-model assumption: abstract machine cycles charged per forward or inverse
permutation syscall. This is a benchmark price, not a measured hardware cycle count. -/
def PERMUTATION_CYCLES : Nat := 8

/-- The combined score covers one full commitment and an opening of this many leaves. -/
def BATCH : Nat := 128

/-- Maximum instructions supplied to any machine run. Cutoff is never successful. -/
def STEP_LIMIT : Nat := 2 ^ 48

/-- An adversary making at most `q ≥ 1` oracle calls breaks binding with probability at most
`q / 2 ^ BINDING_SECURITY_BITS`. -/
def BINDING_SECURITY_BITS : Nat := 120

/-- Statistical hiding security parameter. -/
def HIDING_SECURITY_BITS : Nat := 120

/-- Statistical hiding bound for `q` opened positions and `t` adversary queries.
The query-only target is uniform in `q`; each cardinality still has its own adversary class.
It does not assert a single oracle-dependent-cardinality experiment. The extra one permits
nonzero error at zero queries.
This is a challenge requirement, not a bound proved for a construction. -/
noncomputable def HIDING_ERROR (_q t : Nat) : ℝ :=
  min 1 (((t : ℝ) + 1) / 2 ^ HIDING_SECURITY_BITS)

/-! ### Honest budgets, in oracle calls -/

def COMMIT_BUDGET : Nat := 100 * LENGTH

/-- For an opening of `k` positions. -/
def OPEN_BUDGET (k : Nat) : Nat := 100 * k

/-- For checking an honest opening of `k` positions. -/
def CHECK_BUDGET (k : Nat) : Nat := 100 * k

/-! ### Objects -/

/-- A vector entry, an element of the alphabet `Σ` of [CY24]. -/
abbrev Entry := BitVec LEAF_SIZE

/-- The commitment `rt`. -/
abbrev Commitment := BitVec DIGEST_BITS

/-- A position `0, …, LENGTH - 1`. -/
abbrev Index := Fin LENGTH

/-- A set `I` of positions to open. -/
abbrev Positions := Finset Index

/-- A committed vector `m ∈ Σ^ℓ`. -/
abbrev Message := Index → Entry

/-- Claimed values `a ∈ Σ^I`. -/
abbrev Values (positions : Positions) := positions → Entry

abbrev Byte := BitVec 8

/-- An opening proof: a byte string of any length. -/
abbrev Proof := List Byte

/-- `m[I]`, the message restricted to `I`. -/
def Message.restrict (message : Message) (positions : Positions) : Values positions :=
  fun i => message i

end CommitGolf
