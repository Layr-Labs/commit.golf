import CommitGolfCandidate.ReconstructedBindingCount

namespace CommitGolfCandidate.Reconstruction.Binding
open Finset
set_option maxRecDepth 4096
set_option maxHeartbeats 900000
attribute [local irreducible] Finset.univ
attribute [local instance] Classical.propDecidable
noncomputable section

/-- Recognition uses only the state preceding the sampled reply. -/
def readySeed (m : Table) (k : Key) : Option Seed :=
  if ex : ∃ s, Ready m k s then some ex.choose else none

def weight (m : Table) (k : Key) := ((readySeed m k).map (fun s => work s.depth)).getD 0

theorem ready_chosen (m : Table) (safe : DistinctAnswers m) (k : Key) (s : Seed)
    (h : Ready m k s) : readySeed m k = some s := by
  unfold readySeed
  split
  next ex => exact congrArg some (ready_unique m safe _ _ _ _ ex.choose_spec h).1
  next nex => exact False.elim (nex ⟨s,h⟩)

theorem chosen_ready {m : Table} {k : Key} {s : Seed} (chosen : readySeed m k = some s) :
    Ready m k s := by
  unfold readySeed at chosen
  split at chosen
  next ex => exact Option.some.inj chosen ▸ ex.choose_spec
  next _ => contradiction

theorem weight_le (m : Table) (k : Key) : weight m k ≤ 9 := by
  unfold weight
  cases h : readySeed m k with
  | none => decide
  | some s => exact (by decide : ∀ d : Fin 24, work d ≤ 9) s.depth

theorem mass_put (m : Table) (k : Key) (y : Digest)
    (safe : DistinctAnswers m) (fresh : m k = none)
    (newUnary : m (unary y) = none) (noSelf : unary y ≠ k) :
    mass (put m k y) = mass m + weight m k := by
  classical
  have decompose := complete_put_set m k y fresh newUnary noSelf
  unfold mass
  rw [decompose]
  cases h : readySeed m k with
  | none =>
    have empty : Finset.univ.filter (Ready m k) = ∅ := by
      ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun r => by have := ready_chosen m safe k s r; simp [h] at this
    simp only [empty,Finset.union_empty,weight,h,Option.map_none,Option.getD_none,Nat.add_zero]
  | some s =>
    have only : Finset.univ.filter (Ready m k) = {s} := by
      ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun r => Option.some.inj ((ready_chosen m safe k t r).symm.trans h),
             fun eq => eq ▸ chosen_ready h⟩
    have absent : s ∉ completed m := by
      intro inside
      obtain ⟨y,done⟩ := (mem_completed (m := m) (s := s)).1 inside
      obtain ⟨j,r,seen⟩ := Option.bind_eq_some_iff.1 done
      have eq := Option.some.inj (r.symm.trans (chosen_ready h))
      subst j; simp [fresh] at seen
    rw [only, Finset.union_comm, Finset.singleton_union, Finset.sum_insert absent]
    simp [weight,h, Nat.add_comm]

end
end CommitGolfCandidate.Reconstruction.Binding
