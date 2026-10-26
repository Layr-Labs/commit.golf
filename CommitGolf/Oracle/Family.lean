import CommitGolf.Oracle.IdealPermutation
import CommitGolf.Oracle.IdealCompression
import CommitGolf.Oracle.RandomOracleFixedOutput

/-! # Independent oracle instances and tracks

A family is a finite tree. `sum F G` exposes its instances through `.inl` and `.inr`, and samples
both sides independently, even if their declarations are identical. The track certificate
requires every instance to belong to the selected track. Widths are in bits. -/
namespace CommitGolf
open OracleComp OracleSpec

inductive Track where
  | idealPermutation
  | idealCompression
  | randomOracleFixedOutput
  deriving DecidableEq, Repr

inductive OracleFamily where
  | permutation (width : Nat) (positive : 0 < width)
  | compression (inputBits outputBits : Nat) (positive : 0 < outputBits)
      (compressing : outputBits < inputBits)
  | randomOracleFixedOutput (outputBits : Nat) (positive : 0 < outputBits)
  | sum (left right : OracleFamily)
  deriving DecidableEq

namespace OracleFamily

/-- The original single 1600-bit permutation. -/
abbrev baseline : OracleFamily := .permutation WIDTH (by decide)

/-- A track permits any finite, nonempty collection of its own primitive. -/
def InTrack : OracleFamily → Track → Prop
  | .permutation _ _, track => track = .idealPermutation
  | .compression _ _ _ _, track => track = .idealCompression
  | .randomOracleFixedOutput _ _, track => track = .randomOracleFixedOutput
  | .sum F G, track => F.InTrack track ∧ G.InTrack track

instance instDecidableInTrack (F : OracleFamily) (track : Track) : Decidable (F.InTrack track) :=
  match F with
  | .permutation _ _ => inferInstanceAs (Decidable (track = .idealPermutation))
  | .compression _ _ _ _ => inferInstanceAs (Decidable (track = .idealCompression))
  | .randomOracleFixedOutput _ _ => inferInstanceAs (Decidable (track = .randomOracleFixedOutput))
  | .sum F G => @instDecidableAnd _ _ (F.instDecidableInTrack track) (G.instDecidableInTrack track)

abbrev Domain : OracleFamily → Type
  | .permutation n _ => BitVec n ⊕ BitVec n
  | .compression n _ _ _ => BitVec n
  | .randomOracleFixedOutput _ _ => RandomOracleFixedOutput.Input
  | .sum F G => F.Domain ⊕ G.Domain

/-- The public interface, without private coins. -/
abbrev spec : (F : OracleFamily) → OracleSpec F.Domain
  | .permutation n _ => IdealPermutation.Spec n
  | .compression n k _ _ => IdealCompression.Spec n k
  | .randomOracleFixedOutput m _ => RandomOracleFixedOutput.Spec m
  | .sum F G => F.spec + G.spec

abbrev world (F : OracleFamily) := unifSpec + F.spec

/-- A fixed realization of all instances. Permutations must be bijections. -/
abbrev Realization : OracleFamily → Type
  | .permutation n _ => IdealPermutation.Function n
  | .compression n k _ _ => IdealCompression.Function n k
  | .randomOracleFixedOutput m _ => RandomOracleFixedOutput.Function m
  | .sum F G => F.Realization × G.Realization

/-- Whole-function sampling is available only for finite-domain families. -/
def Finite : OracleFamily → Prop
  | .permutation _ _ | .compression _ _ _ _ => True
  | .randomOracleFixedOutput _ _ => False
  | .sum F G => F.Finite ∧ G.Finite

instance decidableFinite (F : OracleFamily) : Decidable F.Finite :=
  match F with
  | .permutation _ _ => isTrue trivial
  | .compression _ _ _ _ => isTrue trivial
  | .randomOracleFixedOutput _ _ => isFalse id
  | .sum F G => @instDecidableAnd _ _ F.decidableFinite G.decidableFinite

/-- Independent uniform sampling of finite-domain instances. -/
def sample : (F : OracleFamily) → (h : F.Finite := by decide) → ProbComp F.Realization
  | .permutation n _, _ => IdealPermutation.sample n
  | .compression n k _ _, _ => IdealCompression.sample n k
  | .randomOracleFixedOutput _ _, h => False.elim h
  | .sum F G, h => do return (← F.sample h.1, ← G.sample h.2)

def answer {m : Type → Type} [Monad m] :
    (F : OracleFamily) → F.Realization → QueryImpl F.spec m
  | .permutation _ _, π => fun q => match q with
    | .inl x => pure (π x)
    | .inr y => pure (π.symm y)
  | .compression _ _ _ _, H => fun q => pure (H q)
  | .randomOracleFixedOutput _ _, H => fun q => pure (H q)
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

/-- Finite-domain primitives keep a sampled realization; random oracles keep a cache.
A sum keeps separate state for each instance, even when their widths are identical. -/
abbrev State : OracleFamily → Type
  | .permutation n _ => IdealPermutation.Function n
  | .compression n m _ _ => IdealCompression.Function n m
  | .randomOracleFixedOutput m _ => RandomOracleFixedOutput.Cache m
  | .sum F G => F.State × G.State

def initialState : (F : OracleFamily) → ProbComp F.State
  | .permutation n _ => IdealPermutation.sample n
  | .compression n m _ _ => IdealCompression.sample n m
  | .randomOracleFixedOutput _ _ => pure ∅
  | .sum F G => do return (← F.initialState, ← G.initialState)

/-- A shared, stateful oracle handler. State persists across all phases of an experiment. -/
def sharedAnswer : (F : OracleFamily) → QueryImpl F.spec (StateT F.State ProbComp)
  | .permutation _ _ => fun q => match q with
      | .inl x => do return (← get) x
      | .inr y => do return (← get).symm y
  | .compression _ _ _ _ => fun q => do return (← get) q
  | .randomOracleFixedOutput m _ => RandomOracleFixedOutput.answer m
  | .sum F G => fun q => match q with
      | .inl x => do
          let (sF, sG) ← get
          let (y, sF') ← liftM ((F.sharedAnswer x).run sF)
          set (sF', sG)
          return y
      | .inr x => do
          let (sF, sG) ← get
          let (y, sG') ← liftM ((G.sharedAnswer x).run sG)
          set (sF, sG')
          return y

/-- Count public queries while running against the shared state; private coins are free. -/
def runShared (F : OracleFamily) {α : Type} (c : OracleComp F.world α) :
    StateT F.State ProbComp (α × Nat) :=
  (simulateQ ((HasQuery.toQueryImpl (spec := unifSpec) (m := StateT F.State ProbComp) +
    F.sharedAnswer).withAddCost F.callCost) c).run

/-- Checks use the same state but their queries do not increase the adversary's budget. -/
def checkShared (F : OracleFamily) {α : Type} (c : OracleComp F.spec α) :
    StateT F.State ProbComp α := simulateQ F.sharedAnswer c

end OracleFamily
end CommitGolf
