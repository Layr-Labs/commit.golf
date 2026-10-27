import Mathlib.Data.FinEnum
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Real.Basic

/-! # Parameters

Constants and object types, following [CY24, Chapter 18]. Files, in order: `Parameters`,
`Oracle`, `Scheme`, `Honest`, `Binding`, `Statements`. -/

namespace CommitGolf

/-! ### Sizes -/

/-- Width of the permutation in bits: the Keccak-f[1600] state. -/
def WIDTH : Nat := 1600

/-- Bytes in an entry and in a commitment. -/
def DIGEST_BYTES : Nat := 32

def DIGEST_BITS : Nat := 8 * DIGEST_BYTES

def LOG_LENGTH : Nat := 24

/-- Entries in a committed vector, `ℓ = 2 ^ 24`. -/
def LENGTH : Nat := 2 ^ LOG_LENGTH

/-! ### Scoring and security -/

/-- Both scores are measured on honest openings of exactly `BATCH` positions. -/
def BATCH : Nat := 100

/-- An adversary making at most `q ≥ 1` oracle calls breaks binding with probability at most
`q / 2 ^ SECURITY_BITS`. -/
def SECURITY_BITS : Nat := 128

/-! ### Hiding (provisional challenge policy) -/

/-- Draft statistical hiding target; independent of the binding security parameter. -/
def HIDING_SECURITY_BITS : Nat := 128

/-- Provisional bound for `q` opened positions and `t` adversary queries.
The query-only target is uniform in `q`; the extra one permits nonzero error at zero queries.
This is a challenge requirement pending review, not a bound proved for a construction. -/
noncomputable def HIDING_ERROR (_q t : Nat) : ℝ :=
  min 1 (((t : ℝ) + 1) / 2 ^ HIDING_SECURITY_BITS)

/-! ### Honest budgets, in oracle calls -/

def COMMIT_BUDGET : Nat := 100 * LENGTH

/-- For an opening of `k` positions. -/
def OPEN_BUDGET (k : Nat) : Nat := 100 * k

/-- For checking an honest opening of `k` positions. -/
def CHECK_BUDGET (k : Nat) : Nat := 100 * k

/-! ### Objects -/

/-- A state of the permutation. -/
abbrev State := BitVec WIDTH

/-- A vector entry, an element of the alphabet `Σ` of [CY24]. -/
abbrev Entry := BitVec DIGEST_BITS

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
