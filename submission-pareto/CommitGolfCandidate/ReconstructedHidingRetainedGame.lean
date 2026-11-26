import CommitGolfCandidate.ReconstructedHidingTrack

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingReplay HidingTraffic CommitGolfCandidate.Permutation
open CommitGolfCandidate.Permutation.NonceChain (mean Fresh)
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048
local instance keptDiscrete {α : Type} : MeasurableSpace α := ⊤
noncomputable local instance keptKey : SampleableType Key := by classical exact SampleableType.ofFintype _
noncomputable local instance keptReplies : SampleableType GenReplies := by classical exact SampleableType.ofFintype _

noncomputable def genPermit (k : Key) (y : GenReplies) (a b : Reply) : Bool := by
  exact @decide ((∀ j, packedAddress k j ≠ a) ∧ (∀ j, y j ≠ b)) (Classical.propDecidable _)

theorem gen_permit_iff (k : Key) (y : GenReplies) (a b : Reply) :
    genPermit k y a b=true ↔ ((∀ j, packedAddress k j ≠ a) ∧ (∀ j, y j ≠ b)) :=
  @decide_eq_true_iff _ (Classical.propDecidable _)

attribute [local irreducible] packedAddress blockSplit Fresh

theorem safe_schedule (k : Key) (y : GenReplies) (t : Trace Reply) (unique : Function.Injective y)
    (safe : cleanTrace (genPermit k y) t) : Fresh (scheduled (packedAddress k) y) t := by
  unfold scheduled
  apply scheduled_fresh (packedAddress k) y t (fun a b eq => (packedAddress_unique k k a b eq).2) unique
  · intro j found
    obtain ⟨e,seen,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp found)
    exact ((gen_permit_iff _ _ _ _).mp (safe e seen)).1 j eq.symm
  · intro j found
    obtain ⟨e,seen,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp found)
    exact ((gen_permit_iff _ _ _ _).mp (safe e seen)).2 j eq.symm

noncomputable def markedIndependent {A : Type} (c : Compression) (g : PrivateSalts → OracleComp World A) :
    ProbComp (A × Bool) := by
  classical
  exact do
    let k ← $ᵗ Key
    let y ← $ᵗ GenReplies
    let π ← $ᵗ Perm
    let run ← fixedOracleRun ⟨c,π⟩ (checkedQueries (genPermit k y) (g (tapeFromReplies y)) true)
    pure (run.1,run.2 && decide (Function.Injective y))

/-- An independent table, with its actual query instrumentation retained, gives
a common source of mass for the game using the generator's shared permutation. -/
theorem marked_event_le {A : Type} (c : Compression) (g : PrivateSalts → OracleComp World A)
    (ev : A → Prop) :
    (Pr{let v ← markedIndependent c g}[ev v.1 ∧ v.2=true]).toReal ≤
      (Pr{let a ← keyedGame c g}[ev a]).toReal := by
  classical
  let keep (k : Key) (y : GenReplies) (st : GenTrace) :=
    Function.Injective y ∧ cleanTrace (genPermit k y) st.trace
  have lower := retained_event_le c g ev keep (fun k y st h => safe_schedule k y st.trace h.1 h.2)
  refine le_trans ?_ lower
  apply le_of_eq
  unfold markedIndependent retainedEvent
  rw [uniform_bind_mean]
  apply avg_congr
  intro k _
  rw [uniform_bind_mean]
  apply avg_congr
  intro y _
  rw [uniform_bind_mean,←Strat.avg_eager]
  apply avg_congr
  intro π _
  let check := checkedQueries (genPermit k y) (g (tapeFromReplies y)) true
  let post (v : A × Bool) := (v.1,v.2 && decide (Function.Injective y))
  let e := fun (a : A) => ev a ∧ Function.Injective y
  have eval : (fun v : A × Bool => ev (post v).1 ∧ (post v).2=true) =
      (fun v => e v.1 ∧ v.2=true) := by
    funext v
    apply propext
    simp only [post,e,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨fun h => ⟨⟨h.1,h.2.2⟩,h.2.1⟩,fun h => ⟨h.1.1,h.2,h.1.2⟩⟩
  change (Pr{let v ← (fixedOracleRun ⟨c,π⟩ check >>= fun v => pure (post v))}[ev v.1 ∧ v.2=true]).toReal = _
  rw [bind_pure_comp,prEvent_map,eval,fixed_run_prob c π check _ PState.init,ENNReal.toReal_ofReal
    (Strat.eager_nonneg π (fun _ _ => ind_nonneg _) _ _)]
  refine (checked_eager (genPermit k y) c π (g (tapeFromReplies y)) e PState.init true
    (by intro _ h; cases h) (by simp [cleanTrace,PState.init])).trans ?_
  apply congrArg ((toStrat c (g (tapeFromReplies y))).eager π PState.init)
  funext a st
  simp only [e,keep,and_assoc]

end CommitGolfCandidate.Reconstruction.HidingTape
