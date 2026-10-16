import Mathlib.Data.FinEnum
import Mathlib.Data.ENNReal.Inv

/-! # Parameters

The competition's constants and object types. The files read in order: `Parameters`, `Oracle`
(the permutation and call counting), `Scheme`, `Honest` (the honest run), `Binding` (the game),
and `Statements` (the certificate). The definitions follow [CY24, Chapter 18] (Chiesa and Yogev,
*Building Cryptographic Proofs from Hash Functions*), with `MT.Commit`, `MT.Open`, and `MT.Check`
renamed `commit`, `opening`, and `check`. -/

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

/-- An adversary making at most `q ≥ 1` permutation calls breaks binding with probability at most
`q / 2 ^ SECURITY_BITS`. -/
def SECURITY_BITS : Nat := 128

/-! ### Honest budgets, in permutation calls

They hold in the worst case and rule out only absurd designs. `check` is budgeted on honest
openings only. -/

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

/-- Claimed values `a ∈ Σ^I`: one entry at each position of `I`, and nothing else. -/
abbrev Values (positions : Positions) := positions → Entry

abbrev Byte := BitVec 8

/-- An opening proof: a byte string of any length. Its length is the first score. -/
abbrev Proof := List Byte

/-- `m[I]`, the message restricted to `I`. -/
def Message.restrict (message : Message) (positions : Positions) : Values positions :=
  fun i => message i

end CommitGolf
