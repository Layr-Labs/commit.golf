import CommitGolf.Oracle
import Mathlib.Data.Fintype.BigOperators

/-! Query-graph work accounting, before probabilistic bad-event estimates. -/
namespace CommitGolfCandidate.Chained
open scoped BigOperators

abbrev Height := Fin 24
abbrev Seed := BitVec 476
abbrev Input := BitVec 512
abbrev Output := BitVec 256

structure Encoding where
  first : Height → Seed → Input
  next : Height → Nat → Output → Input
  tag : Input → Option (Height × Nat)
  link : Input → Option Output
  first_tag : ∀ h seed, tag (first h seed) = some (h, 0)
  next_tag : ∀ h j value, 0 < j → j < 8 → tag (next h j value) = some (h, j)
  next_link : ∀ h j value, 0 < j → j < 8 → link (next h j value) = some value
  first_injective : ∀ h, Function.Injective (first h)
  next_injective : ∀ h j, 0 < j → j < 8 → Function.Injective (next h j)

structure Trace where
  size : Nat
  input : Fin size → Input
  output : Fin size → Output
  fresh : Function.Injective input

structure Good (enc : Encoding) (trace : Trace) : Prop where
  outputs : Function.Injective trace.output
  no_guesses : ∀ (earlier later : Fin trace.size), earlier.val < later.val →
    ∀ h j value, 0 < j → j < 8 → trace.input earlier = enc.next h j value →
      trace.output later ≠ value

structure Evaluation (enc : Encoding) (calls : Height → Nat) (trace : Trace) where
  height : Height
  seed : Seed
  positive : 0 < calls height
  bounded : calls height ≤ 8
  row : Nat → Fin trace.size
  first : trace.input (row 0) = enc.first height seed
  next : ∀ j, j+1 < calls height →
    trace.input (row (j+1)) = enc.next height (j+1) (trace.output (row j))

namespace Evaluation
variable {enc : Encoding} {calls : Height → Nat} {trace : Trace}

def identity (e : Evaluation enc calls trace) : Height × Seed := (e.height, e.seed)

theorem tagged (e : Evaluation enc calls trace) (j : Nat) (inside : j < calls e.height) :
    enc.tag (trace.input (e.row j)) = some (e.height, j) := by
  have bound := e.bounded
  cases j with
  | zero => rw [e.first, enc.first_tag]
  | succ j => rw [e.next j inside, enc.next_tag _ _ _ (by omega) (by omega)]

theorem stage_eq_of_shared (e f : Evaluation enc calls trace) (j k : Nat)
    (ej : j < calls e.height) (fk : k < calls f.height) (same : e.row j = f.row k) :
    e.height = f.height ∧ j = k := by
  have tags := congrArg (fun row => enc.tag (trace.input row)) same
  rw [e.tagged j ej, f.tagged k fk] at tags
  exact Prod.mk.inj (Option.some.inj tags)

theorem row_injective (e : Evaluation enc calls trace) :
    Function.Injective (fun j : Fin (calls e.height) => e.row j.val) := by
  intro j k same
  exact Fin.ext (e.stage_eq_of_shared e j.val k.val j.isLt k.isLt same).2

theorem seed_eq_of_shared (good : Good enc trace) (e f : Evaluation enc calls trace)
    (height : e.height = f.height) (j : Nat) (inside : j < calls e.height)
    (same : e.row j = f.row j) : e.seed = f.seed := by
  induction j with
  | zero =>
    have inputs := congrArg trace.input same
    rw [e.first, f.first, ← height] at inputs
    exact enc.first_injective e.height inputs
  | succ j ih =>
    have bound := e.bounded
    have other : j+1 < calls f.height := by simpa only [height] using inside
    have inputs := congrArg trace.input same
    rw [e.next j inside, f.next j other, ← height] at inputs
    have previous := good.outputs (enc.next_injective e.height (j+1) (by omega) (by omega) inputs)
    exact ih (by omega) previous

theorem identity_eq_of_shared (good : Good enc trace) (e f : Evaluation enc calls trace)
    (j k : Nat) (ej : j < calls e.height) (fk : k < calls f.height)
    (same : e.row j = f.row k) : e.identity = f.identity := by
  obtain ⟨height, stages⟩ := e.stage_eq_of_shared f j k ej fk same
  subst k
  exact Prod.ext height (seed_eq_of_shared good e f height j ej same)

theorem ordered (good : Good enc trace) (e : Evaluation enc calls trace)
    (j : Nat) (inside : j+1 < calls e.height) : (e.row j).val < (e.row (j+1)).val := by
  have bound := e.bounded
  have different : e.row j ≠ e.row (j+1) := by
    intro same
    have impossible := (e.stage_eq_of_shared e j (j+1) (by omega) inside same).2
    omega
  have unequal : (e.row j).val ≠ (e.row (j+1)).val := by
    intro same
    exact different (Fin.ext same)
  by_contra backwards
  have lt : (e.row (j+1)).val < (e.row j).val := by omega
  exact good.no_guesses (e.row (j+1)) (e.row j) lt e.height (j+1)
    (trace.output (e.row j)) (by omega) (by omega) (e.next j inside) rfl

end Evaluation

theorem disjoint_work {enc : Encoding} {calls : Height → Nat} {trace : Trace}
    (good : Good enc trace) {count : Nat} (family : Fin count → Evaluation enc calls trace)
    (distinct : Function.Injective (fun i => (family i).identity)) :
    Function.Injective (fun slot : (i : Fin count) × Fin (calls (family i).height) =>
      (family slot.1).row slot.2.val) := by
  intro a b same
  obtain ⟨i,j⟩ := a
  obtain ⟨k,l⟩ := b
  have identities := Evaluation.identity_eq_of_shared good (family i) (family k)
    j.val l.val j.isLt l.isLt same
  have indices := distinct identities
  subst k
  have stages := (family i).row_injective same
  change j = l at stages
  cases stages
  rfl

theorem completed_work_bound {enc : Encoding} {calls : Height → Nat} {trace : Trace}
    (good : Good enc trace) {count : Nat} (family : Fin count → Evaluation enc calls trace)
    (distinct : Function.Injective (fun i => (family i).identity)) :
    (∑ i : Fin count, calls (family i).height) ≤ trace.size := by
  have bound := Fintype.card_le_of_injective _ (disjoint_work good family distinct)
  simpa only [Fintype.card_sigma, Fintype.card_fin] using bound

end CommitGolfCandidate.Chained
