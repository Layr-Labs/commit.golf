import CommitGolfCandidate.ChainedFinalTargets

/-! Final-reply hazards intersect good extensions rather than conditioning on them. -/
namespace CommitGolfCandidate.Chained
open CommitGolf OracleComp

def FinalCollision (enc : Encoding) (calls width : Height → Nat) (trace : Trace) : Prop :=
  ∃ h a b, a ≠ b ∧ Completed enc calls trace (h,a) ∧ Completed enc calls trace (h,b) ∧
    lowBits (width h) (finalOutput enc calls trace (h,a)) =
      lowBits (width h) (finalOutput enc calls trace (h,b))

theorem collision_requires_target {enc : Encoding} {calls width : Height → Nat} {trace : Trace}
    {input : Input} {fresh : ∀ i, trace.input i ≠ input} (oldGood : Good enc trace)
    (small : 2*trace.size < 2^256) (safe : ¬ FinalCollision enc calls width trace)
    (height : Height) (seed : Seed) (predicted : prediction enc calls trace input fresh = some (height,seed))
    (reply : Output) (good : Good enc (trace.append input reply fresh))
    (collision : FinalCollision enc calls width (trace.append input reply fresh)) :
    lowBits (width height) reply ∈ finalTargets enc calls trace height (width height) := by
  classical
  obtain ⟨p,identity⟩ := (prediction_some_iff oldGood small (height,seed)).mp predicted
  have newValue : finalOutput enc calls (trace.append input reply fresh) (height,seed) = reply := by
    rw [← identity]
    exact finalOutput_prospective p reply
  obtain ⟨h,a,b,different,ca,cb,equal⟩ := collision
  rcases (completed_prediction (calls := calls) reply good small (h,a)).mp ca with oldA | newA
  · rcases (completed_prediction (calls := calls) reply good small (h,b)).mp cb with oldB | newB
    · apply False.elim
      apply safe
      refine ⟨h,a,b,different,oldA,oldB,?_⟩
      simpa only [finalOutput_stable input reply fresh (h,a) oldA,
        finalOutput_stable input reply fresh (h,b) oldB] using equal
    · obtain ⟨sameHeight,sameSeed⟩ := Prod.mk.inj (Option.some.inj (predicted.symm.trans newB))
      change height = h at sameHeight
      change seed = b at sameSeed
      subst h
      subst b
      rw [finalOutput_stable input reply fresh (height,a) oldA,newValue] at equal
      rw [← equal]
      exact finalTargets_mem height (width height) a oldA
  · rcases (completed_prediction (calls := calls) reply good small (h,b)).mp cb with oldB | newB
    · obtain ⟨sameHeight,sameSeed⟩ := Prod.mk.inj (Option.some.inj (predicted.symm.trans newA))
      change height = h at sameHeight
      change seed = a at sameSeed
      subst h
      subst a
      rw [newValue,finalOutput_stable input reply fresh (height,b) oldB] at equal
      rw [equal]
      exact finalTargets_mem height (width height) b oldB
    · exact (different (congrArg Prod.snd (Option.some.inj (newA.symm.trans newB)))).elim

theorem no_prediction_safe {enc : Encoding} {calls width : Height → Nat} {trace : Trace}
    {input : Input} {fresh : ∀ i, trace.input i ≠ input} (small : 2*trace.size < 2^256)
    (safe : ¬ FinalCollision enc calls width trace) (predicted : prediction enc calls trace input fresh = none)
    (reply : Output) (good : Good enc (trace.append input reply fresh)) :
    ¬ FinalCollision enc calls width (trace.append input reply fresh) := by
  rintro ⟨h,a,b,different,ca,cb,equal⟩
  have oldA : Completed enc calls trace (h,a) := by
    simpa only [predicted,reduceCtorEq,or_false] using
      (completed_prediction (calls := calls) reply good small (h,a)).mp ca
  have oldB : Completed enc calls trace (h,b) := by
    simpa only [predicted,reduceCtorEq,or_false] using
      (completed_prediction (calls := calls) reply good small (h,b)).mp cb
  apply safe
  refine ⟨h,a,b,different,oldA,oldB,?_⟩
  simpa only [finalOutput_stable input reply fresh (h,a) oldA,
    finalOutput_stable input reply fresh (h,b) oldB] using equal

noncomputable def finalHazard (enc : Encoding) (calls width : Height → Nat) (trace : Trace)
    (input : Input) (fresh : ∀ i, trace.input i ≠ input) : ENNReal :=
  match prediction enc calls trace input fresh with
  | none => 0
  | some (height,_) => (completedCount enc calls trace height : ENNReal)/2^(width height)

theorem fresh_final_hazard {enc : Encoding} {calls width : Height → Nat} {trace : Trace}
    {input : Input} {fresh : ∀ i, trace.input i ≠ input} (oldGood : Good enc trace)
    (small : 2*trace.size < 2^256) (safe : ¬ FinalCollision enc calls width trace)
    (widthBound : ∀ h, width h ≤ 256) :
    Pr{let reply ← $ᵗ Output}[Good enc (trace.append input reply fresh) ∧
      FinalCollision enc calls width (trace.append input reply fresh)] ≤
      finalHazard enc calls width trace input fresh := by
  classical
  cases predicted : prediction enc calls trace input fresh with
  | none =>
    have impossible : ∀ reply, ¬ (Good enc (trace.append input reply fresh) ∧
        FinalCollision enc calls width (trace.append input reply fresh)) := by
      rintro reply ⟨good,collision⟩
      exact no_prediction_safe small safe predicted reply good collision
    simp only [finalHazard,predicted]
    calc
      _ ≤ Pr{let _ ← $ᵗ Output}[False] := prEvent_mono_of_support _ _ _ fun reply _ event =>
        (impossible reply event).elim
      _ = 0 := by simp
  | some id =>
    obtain ⟨height,seed⟩ := id
    simp only [finalHazard,predicted]
    calc
      _ ≤ Pr{let reply ← $ᵗ Output}[lowBits (width height) reply ∈ finalTargets enc calls trace height (width height)] :=
        prEvent_mono_of_support _ _ _ fun reply _ event =>
          collision_requires_target oldGood small safe height seed predicted reply event.1 event.2
      _ ≤ _ := finalTargets_probability enc calls trace height (width height) (widthBound height)

end CommitGolfCandidate.Chained
