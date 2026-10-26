import CommitGolf.Oracle.IdealPermutation
import CommitGolf.Oracle.IdealCompression

/-! # Independent oracle instances and tracks

A family is a finite tree. `sum F G` exposes its instances through `.inl` and `.inr`, and samples
both sides independently, even if their declarations are identical. The track certificate
requires every instance to belong to the selected track. Widths are in bits. -/
namespace CommitGolf
open OracleComp OracleSpec

inductive Track where
  | idealPermutation
  | idealCompression
  deriving DecidableEq, Repr

inductive OracleFamily where
  | permutation (width : Nat) (positive : 0 < width)
  | compression (inputBits outputBits : Nat) (positive : 0 < outputBits)
      (compressing : outputBits < inputBits)
  | sum (left right : OracleFamily)
  deriving DecidableEq

namespace OracleFamily

/-- The original single 1600-bit permutation. -/
abbrev baseline : OracleFamily := .permutation WIDTH (by decide)

/-- A track permits any finite, nonempty collection of its own primitive. -/
def InTrack : OracleFamily → Track → Prop
  | .permutation _ _, track => track = .idealPermutation
  | .compression _ _ _ _, track => track = .idealCompression
  | .sum F G, track => F.InTrack track ∧ G.InTrack track

instance instDecidableInTrack (F : OracleFamily) (track : Track) : Decidable (F.InTrack track) :=
  match F with
  | .permutation _ _ => inferInstanceAs (Decidable (track = .idealPermutation))
  | .compression _ _ _ _ => inferInstanceAs (Decidable (track = .idealCompression))
  | .sum F G => @instDecidableAnd _ _ (F.instDecidableInTrack track) (G.instDecidableInTrack track)

abbrev Domain : OracleFamily → Type
  | .permutation n _ => BitVec n ⊕ BitVec n
  | .compression n _ _ _ => BitVec n
  | .sum F G => F.Domain ⊕ G.Domain

/-- The public interface, without private coins. -/
abbrev spec : (F : OracleFamily) → OracleSpec F.Domain
  | .permutation n _ => IdealPermutation.Spec n
  | .compression n k _ _ => IdealCompression.Spec n k
  | .sum F G => F.spec + G.spec

abbrev world (F : OracleFamily) := unifSpec + F.spec

/-- A fixed realization of all instances. Permutations must be bijections. -/
abbrev Realization : OracleFamily → Type
  | .permutation n _ => IdealPermutation.Function n
  | .compression n k _ _ => IdealCompression.Function n k
  | .sum F G => F.Realization × G.Realization

/-- Independent uniform sampling of all declared instances. -/
def sample : (F : OracleFamily) → ProbComp F.Realization
  | .permutation n _ => IdealPermutation.sample n
  | .compression n k _ _ => IdealCompression.sample n k
  | .sum F G => do return (← F.sample, ← G.sample)

def answer {m : Type → Type} [Monad m] :
    (F : OracleFamily) → F.Realization → QueryImpl F.spec m
  | .permutation _ _, π => fun q => match q with
    | .inl x => pure (π x)
    | .inr y => pure (π.symm y)
  | .compression _ _ _ _, H => fun q => pure (H q)
  | .sum F G, H => F.answer H.1 (m := m) + G.answer H.2 (m := m)

/-- Every public query costs one, including repeats and inverse queries; coins are free. -/
def callCost (F : OracleFamily) : F.world.Domain → Nat
  | .inl _ => 0
  | .inr _ => 1

def run (F : OracleFamily) (H : F.Realization) {α : Type}
    (c : OracleComp F.world α) : ProbComp (α × Nat) :=
  (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) +
    F.answer H (m := ProbComp)).withAddCost F.callCost) c).run

def eval (F : OracleFamily) (H : F.Realization) {α : Type}
    (c : OracleComp F.spec α) : α × Nat :=
  (simulateQ ((F.answer H (m := Id)).withAddCost fun _ => 1) c).run

end OracleFamily
end CommitGolf
