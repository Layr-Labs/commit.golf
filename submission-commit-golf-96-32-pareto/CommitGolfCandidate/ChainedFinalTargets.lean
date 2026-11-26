import CommitGolfCandidate.ChainedCompletionCounter
import CommitGolfCandidate.LowBitsUniform

/-! Old final-output targets have the cardinality charged by the completion counter. -/
namespace CommitGolfCandidate.Chained
open CommitGolf OracleComp

noncomputable def finalOutput (enc : Encoding) (calls : Height → Nat) (trace : Trace) (id : Height × Seed) : Output := by
  classical
  exact if available : Completed enc calls trace id then
    trace.output ((Classical.choose available).row (calls id.1-1)) else 0

theorem finalOutput_of_evaluation {enc : Encoding} {calls : Height → Nat} {trace : Trace}
    (e : Evaluation enc calls trace) :
    finalOutput enc calls trace e.identity = trace.output (e.row (calls e.height-1)) := by
  classical
  let available : Completed enc calls trace e.identity := ⟨e,rfl⟩
  rw [finalOutput,dif_pos available]
  apply congrArg trace.output
  apply Evaluation.row_eq_of_identity (Classical.choose available) e (Classical.choose_spec available)
  have height := congrArg Prod.fst (Classical.choose_spec available)
  change (Classical.choose available).height = e.height at height
  change calls e.height-1 < calls (Classical.choose available).height
  rw [height]
  have := e.positive
  omega

theorem finalOutput_stable {enc : Encoding} {calls : Height → Nat} {trace : Trace}
    (input : Input) (reply : Output) (fresh : ∀ i, trace.input i ≠ input) (id : Height × Seed)
    (complete : Completed enc calls trace id) :
    finalOutput enc calls (trace.append input reply fresh) id = finalOutput enc calls trace id := by
  obtain ⟨e,same⟩ := complete
  subst id
  rw [show e.identity = (e.lift input reply fresh).identity from rfl,
    finalOutput_of_evaluation (e.lift input reply fresh),
    show (e.lift input reply fresh).identity = e.identity from rfl,finalOutput_of_evaluation e]
  simp only [Evaluation.lift,Trace.append,extend,Fin.val_castSucc,dif_pos (e.row (calls e.height-1)).isLt]

theorem finalOutput_prospective {enc : Encoding} {calls : Height → Nat} {trace : Trace}
    {input : Input} {fresh : ∀ i, trace.input i ≠ input} (p : Prospective enc calls trace input fresh)
    (reply : Output) : finalOutput enc calls (trace.append input reply fresh) p.identity = reply := by
  have value := finalOutput_of_evaluation (p.evaluate reply)
  change finalOutput enc calls (trace.append input reply fresh) p.identity =
    (trace.append input reply fresh).output (p.evaluation.row (calls p.evaluation.height-1)) at value
  rw [p.last] at value
  simpa [Trace.append,extend] using value

noncomputable def finalTargets (enc : Encoding) (calls : Height → Nat) (trace : Trace)
    (h : Height) (width : Nat) : Finset (BitVec width) := by
  classical
  exact (completedSeeds enc calls trace h).toFinite.toFinset.image
    (fun seed => lowBits width (finalOutput enc calls trace (h,seed)))

theorem finalTargets_mem {enc : Encoding} {calls : Height → Nat} {trace : Trace}
    (h : Height) (width : Nat) (seed : Seed) (complete : Completed enc calls trace (h,seed)) :
    lowBits width (finalOutput enc calls trace (h,seed)) ∈ finalTargets enc calls trace h width := by
  classical
  exact Finset.mem_image.mpr ⟨seed,by simpa only [Set.Finite.mem_toFinset,completedSeeds,Set.mem_setOf_eq] using complete,rfl⟩

theorem finalTargets_card (enc : Encoding) (calls : Height → Nat) (trace : Trace) (h : Height) (width : Nat) :
    (finalTargets enc calls trace h width).card ≤ completedCount enc calls trace h := by
  classical
  unfold finalTargets completedCount
  calc
    _ ≤ (completedSeeds enc calls trace h).toFinite.toFinset.card := Finset.card_image_le
    _ = _ := (Set.ncard_eq_toFinset_card (completedSeeds enc calls trace h)).symm

theorem finalTargets_probability (enc : Encoding) (calls : Height → Nat) (trace : Trace) (h : Height)
    (width : Nat) (bounded : width ≤ 256) :
    Pr{let reply ← $ᵗ Output}[lowBits width reply ∈ finalTargets enc calls trace h width] ≤
      (completedCount enc calls trace h : ENNReal)/2^width :=
  (uniform_lowBits_targets width bounded _).trans
    (ENNReal.div_le_div_right (Nat.cast_le.mpr (finalTargets_card enc calls trace h width)) _)

end CommitGolfCandidate.Chained
