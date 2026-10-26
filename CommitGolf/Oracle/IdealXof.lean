import CommitGolf.Oracle.RandomOracleFixedOutput

/-! # Ideal extendable-output function

Each finite input identifies an independent random bit stream. A query requests its first
`n` bits, in most-significant-bit order. Internal bit sampling is not a public oracle query:
each request costs one call, including zero-length requests and repeats. -/
namespace CommitGolf.IdealXof
open OracleComp OracleSpec

abbrev Input := List Bool
abbrev Domain := Input × Nat
abbrev Spec : OracleSpec Domain := fun q => BitVec q.2
abbrev Function := Input → Nat → Bool

/-- The cache key excludes requested length, so different lengths share their prefix. -/
abbrev BitSpec : OracleSpec (Input × Nat) := (Input × Nat) →ₒ Bool
abbrev Cache := BitSpec.QueryCache

/-- Read consecutive stream bits, placing the first bit at the most significant position. -/
def readBits {m : Type → Type} [Monad m] (bit : Nat → m Bool)
    (start : Nat) : (n : Nat) → m (BitVec n)
  | 0 => pure 0
  | n + 1 => do
      let b ← bit start
      let tail ← readBits bit (start + 1) n
      return BitVec.cons b tail

/-- Fixed realizations are streams, enforcing prefix consistency also in honest statements. -/
def eval (H : Function) (q : Domain) : BitVec q.2 :=
  readBits (m := Id) (H q.1) 0 q.2

/-- Every requested length reads the same stream positions. -/
theorem readBits_getMsbD (bit : Nat → Bool) (start n i : Nat) (h : i < n) :
    (readBits (m := Id) bit start n).getMsbD i = bit (start + i) := by
  induction n generalizing start i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [readBits, pure, bind]
      | succ i =>
          simp only [readBits, pure, bind, BitVec.getMsbD_cons_succ]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (start + 1) i (by omega)

/-- VCVio samples each previously unseen stream bit uniformly and remembers it. -/
def answer : QueryImpl Spec (StateT Cache ProbComp) := fun q =>
  readBits (fun i => BitSpec.randomOracle (q.1, i)) 0 q.2

end CommitGolf.IdealXof
