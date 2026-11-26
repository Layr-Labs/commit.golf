import CommitGolfCandidate.ChainedCompletion
import Mathlib.Data.Set.Card

/-! Reply-independent prediction and exact per-height completion counter updates. -/
namespace CommitGolfCandidate.Chained
variable {enc : Encoding} {calls : Height → Nat} {trace : Trace} {input : Input}
  {fresh : ∀ i, trace.input i ≠ input}

noncomputable def prediction (enc : Encoding) (calls : Height → Nat) (trace : Trace)
    (input : Input) (fresh : ∀ i, trace.input i ≠ input) : Option (Height × Seed) := by
  classical
  exact if available : Nonempty (Prospective enc calls trace input fresh) then
    some (Classical.choice available).identity else none

theorem prediction_some_iff (good : Good enc trace) (small : 2*trace.size < 2^256)
    (id : Height × Seed) : prediction enc calls trace input fresh = some id ↔
      ∃ p : Prospective enc calls trace input fresh, p.identity = id := by
  classical
  unfold prediction
  split
  · rename_i available
    constructor
    · intro same
      exact ⟨Classical.choice available,Option.some.inj same⟩
    · rintro ⟨p,same⟩
      exact congrArg some ((prospective_unique good small (Classical.choice available) p).trans same)
  · rename_i unavailable
    constructor
    · intro impossible
      contradiction
    · rintro ⟨p,_⟩
      exact (unavailable ⟨p⟩).elim

theorem completed_prediction (reply : Output) (good : Good enc (trace.append input reply fresh))
    (small : 2*trace.size < 2^256) (id : Height × Seed) :
    Completed enc calls (trace.append input reply fresh) id ↔
      Completed enc calls trace id ∨ prediction enc calls trace input fresh = some id := by
  have oldGood := good_of_append enc trace input reply fresh good
  exact (completion_step reply good id).trans
    (or_congr Iff.rfl (prediction_some_iff oldGood small id).symm)

def completedSeeds (enc : Encoding) (calls : Height → Nat) (trace : Trace) (h : Height) : Set Seed :=
  {seed | Completed enc calls trace (h,seed)}

noncomputable def completedCount (enc : Encoding) (calls : Height → Nat) (trace : Trace) (h : Height) : Nat :=
  (completedSeeds enc calls trace h).ncard

def bump (predicted : Option (Height × Seed)) (h : Height) : Nat :=
  match predicted with
  | none => 0
  | some (height,_) => if height = h then 1 else 0

theorem counter_update (reply : Output) (good : Good enc (trace.append input reply fresh))
    (small : 2*trace.size < 2^256) (h : Height) :
    completedCount enc calls (trace.append input reply fresh) h =
      completedCount enc calls trace h + bump (prediction enc calls trace input fresh) h := by
  classical
  have oldGood := good_of_append enc trace input reply fresh good
  cases predicted : prediction enc calls trace input fresh with
  | none =>
    have sets : completedSeeds enc calls (trace.append input reply fresh) h =
        completedSeeds enc calls trace h := by
      ext seed
      change Completed enc calls (trace.append input reply fresh) (h,seed) ↔
        Completed enc calls trace (h,seed)
      simpa only [predicted,reduceCtorEq,or_false] using completed_prediction (calls := calls) reply good small (h,seed)
    change (completedSeeds enc calls (trace.append input reply fresh) h).ncard = _
    rw [sets]
    simp [completedCount,predicted,bump]
  | some id =>
    obtain ⟨height,seed⟩ := id
    obtain ⟨p,same⟩ := (prediction_some_iff oldGood small (height,seed)).mp predicted
    have notOld : seed ∉ completedSeeds enc calls trace height := by
      rintro ⟨e,equal⟩
      exact p.fresh_identity e (same.trans equal.symm)
    by_cases equal : height = h
    · subst h
      have sets : completedSeeds enc calls (trace.append input reply fresh) height =
          insert seed (completedSeeds enc calls trace height) := by
        ext value
        change Completed enc calls (trace.append input reply fresh) (height,value) ↔
          value = seed ∨ Completed enc calls trace (height,value)
        simpa [predicted,eq_comm,or_comm] using completed_prediction (calls := calls) reply good small (height,value)
      change (completedSeeds enc calls (trace.append input reply fresh) height).ncard = _
      rw [sets,Set.ncard_insert_of_notMem notOld]
      simp [completedCount,predicted,bump]
    · have sets : completedSeeds enc calls (trace.append input reply fresh) h =
          completedSeeds enc calls trace h := by
        ext value
        change Completed enc calls (trace.append input reply fresh) (h,value) ↔ Completed enc calls trace (h,value)
        simpa [predicted,equal] using completed_prediction (calls := calls) reply good small (h,value)
      change (completedSeeds enc calls (trace.append input reply fresh) h).ncard = _
      rw [sets]
      simp [completedCount,predicted,bump,equal]

end CommitGolfCandidate.Chained
