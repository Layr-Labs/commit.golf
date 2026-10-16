import Mathlib.Data.FinEnum
import Mathlib.Data.ENNReal.Inv

/-! # Parameters

The competition's constants and the types of the objects a vector commitment scheme handles.

**Reading order.** This is the first of six files; each builds on the previous ones:

1. `Parameters` (this file): constants and object types.
2. `Oracle`: the ideal permutation `π` and how its calls are counted.
3. `Scheme`: the syntax of a vector commitment scheme, `commit`, `opening`, and `check`.
4. `Honest`: the honest commit-open-check run, and the random batch over which scores are averaged.
5. `Binding`: the position-binding game played by an adversary.
6. `Statements`: the five properties a submission proves, bundled as a `Certificate`.

**Source.** The objects follow [CY24, Chapter 18] (Chiesa and Yogev, *Building Cryptographic
Proofs from Hash Functions*), with the Merkle-specific names replaced by generic ones: `MT.Commit`,
`MT.Open`, and `MT.Check` become `commit`, `opening`, and `check`. A message is a vector of
`LENGTH` entries, a commitment is one digest, and an opening proof for a set `I` of positions is a
byte string whose length is one of the two scores. -/

namespace CommitGolf

/-! ### The ideal permutation -/

/-- Width of the ideal permutation `π`, in bits: the state size of Keccak-f[1600], the permutation
behind SHA-3. A state is `WIDTH` bits; how a scheme splits it into rate and capacity is part of the
design. -/
def WIDTH : Nat := 1600

/-! ### The committed vector -/

/-- Bytes in one vector entry and in one commitment: a 32-byte digest. -/
def DIGEST_BYTES : Nat := 32

/-- The same size in bits, `256`. -/
def DIGEST_BITS : Nat := 8 * DIGEST_BYTES

/-- `log₂` of the vector length. -/
def LOG_LENGTH : Nat := 24

/-- Number of entries in a committed vector: `ℓ = 2 ^ 24`. -/
def LENGTH : Nat := 2 ^ LOG_LENGTH

/-! ### Scoring and security -/

/-- Number of distinct positions opened together in the scored opening. Both scores are averages
over a uniformly random set of exactly `BATCH` positions. -/
def BATCH : Nat := 100

/-- Security level of position binding: an adversary making at most `q ≥ 1` permutation calls wins
the binding game with probability at most `q / 2 ^ SECURITY_BITS`. -/
def SECURITY_BITS : Nat := 128

/-! ### Honest budgets, in permutation calls

A call is one query to `π` or to `π⁻¹`. The budgets keep the honest algorithms practical for every
number of opened positions; they are generous on purpose, so that they rule out only absurd designs.
`check` is budgeted only on honest openings: its calls on malformed proofs are unbounded, and its
average number of calls on honest openings of `BATCH` positions is the second score. -/

/-- Calls allowed to `commit`, for every message, every permutation, and all coins: 100 per entry. -/
def COMMIT_BUDGET : Nat := 100 * LENGTH

/-- Calls allowed to `opening` when it opens `k` positions with an honest trapdoor: 100 per opened
position. -/
def OPEN_BUDGET (k : Nat) : Nat := 100 * k

/-- Calls allowed to `check` when it checks an honest opening of `k` positions: 100 per opened
position. -/
def CHECK_BUDGET (k : Nat) : Nat := 100 * k

/-! ### Objects

Entries and commitments are bit vectors rather than byte strings because schemes compute with them
(slice them into permutation states, compare them). Proofs are byte strings because their length in
bytes is scored. -/

/-- A state of the permutation `π`: `WIDTH = 1600` bits. -/
abbrev State := BitVec WIDTH

/-- A vector entry: one element of the alphabet `Σ` of [CY24], a 256-bit string. -/
abbrev Entry := BitVec DIGEST_BITS

/-- A commitment: the `rt` of [CY24], a 256-bit string. -/
abbrev Commitment := BitVec DIGEST_BITS

/-- A position in the vector: `0, 1, …, LENGTH - 1`. -/
abbrev Index := Fin LENGTH

/-- A set `I ⊆ [ℓ]` of positions to open. -/
abbrev Positions := Finset Index

/-- A committed vector `m ∈ Σ^ℓ`: one entry at every position. -/
abbrev Message := Index → Entry

/-- Claimed values `a ∈ Σ^I`: one entry at each position of `I`, and nothing else. Since values
outside `I` are not even representable, `check` cannot read them. -/
abbrev Values (positions : Positions) := positions → Entry

/-- One byte. -/
abbrev Byte := BitVec 8

/-- An opening proof `pf`: a byte string of any length. Its length in bytes is the first score. -/
abbrev Proof := List Byte

/-- `m[I]`: the message restricted to the positions in `I`, as `check` receives it in the honest
run. -/
def Message.restrict (message : Message) (positions : Positions) : Values positions :=
  fun i => message i

end CommitGolf
