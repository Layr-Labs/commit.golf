import CommitGolfCandidate.SharedPinnedRows
import CommitGolfCandidate.SharedOracleCoupling

/-! Adaptive joint programming bounds for both challenge worlds. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
open scoped ENNReal
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
local instance SharedPinnedAdaptiveDiscrete {α : Type} : MeasurableSpace α := ⊤

private theorem shared_programming_agrees (compress : Compression) (p : BiPermutation Block)
    (rows : List (Block × Block)) (query : World.Domain) (unmarked : marksReferencePair p rows query = false) :
    (fixedOracle compress p).world query = (fixedOracle compress (p.programRows rows)).world query := by
  rcases query with coins | (input | (input | output))
  · rfl
  · rfl
  · have disjoint (row) (present : row ∈ rows) :
        input ≠ row.1 ∧ p.forward input ≠ row.2 := by
      apply not_or.mp
      intro hit
      have marked : marksReferencePair p rows (.inr (.inr (.inl input))) = true :=
        List.any_eq_true.mpr ⟨row, present, decide_eq_true hit⟩
      rw [marked] at unmarked
      contradiction
    change (pure (p.forward input) : ProbComp Block) = pure ((p.programRows rows).forward input)
    rw [p.program_rows_forward_unchanged rows input disjoint]
  · have disjoint (row) (present : row ∈ rows) :
        p.inverse output ≠ row.1 ∧ output ≠ row.2 := by
      apply not_or.mp
      intro hit
      have marked : marksReferencePair p rows (.inr (.inr (.inr output))) = true :=
        List.any_eq_true.mpr ⟨row, present, decide_eq_true hit⟩
      rw [marked] at unmarked
      contradiction
    change (pure (p.inverse output) : ProbComp Block) = pure ((p.programRows rows).inverse output)
    rw [p.program_rows_inverse_unchanged rows output disjoint]


private theorem shared_mark_left (p : BiPermutation Block) (left right : List Row)
    (query : World.Domain) (off : marksReferencePair p (left ++ right) query = false) :
    marksReferencePair p left query = false ∧ marksReferencePair p right query = false := by
  rcases query with coins | (input | (input | output))
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · simpa only [marksReferencePair, List.any_append, Bool.or_eq_false_iff] using off
  · simpa only [marksReferencePair, List.any_append, Bool.or_eq_false_iff] using off

theorem shared_adaptive_programmed_distance {α : Type}
    (sample : ProbComp (List Row × List Row)) (rate : ENNReal) (finite : rate ≠ ∞)
    (compress : Compression) (p : BiPermutation Block) (observer : OracleComp World α)
    (budget : Nat) (bounded : QueryBounded observer budget)
    (fixed : ∀ row, Pr{let pair ← sample}[rowHits (pair.1 ++ pair.2) row = true] ≤ rate) :
    measureTVDist
      (sample >>= fun pair => fixedOracleRun (fixedOracle compress (p.programRows pair.1)) observer)
      (sample >>= fun pair => fixedOracleRun (fixedOracle compress (p.programRows pair.2)) observer) ≤
      ((budget : ENNReal) * rate).toReal := by
  let flattened := (fun pair : List Row × List Row => pair.1 ++ pair.2) <$> sample
  have hit := pinned_adaptive_reference_hits flattened rate compress p observer budget bounded
    (fun row => by simpa only [flattened, prEvent_map] using fixed row)
  have bound := distance_averaged_event sample
    (fun pair => fixedOracleRun (fixedOracle compress (p.programRows pair.1)) observer)
    (fun pair => fixedOracleRun (fixedOracle compress (p.programRows pair.2)) observer)
    (fun pair => flaggedRun (fixedOracle compress p) (marksReferencePair p (pair.1 ++ pair.2)) observer)
    (fun result => result.2.2 = true) (by
      intro pair
      have step := SharedOracle.distance_le_reference_hit (fixedOracle compress p)
        (fixedOracle compress (p.programRows pair.1)) (fixedOracle compress (p.programRows pair.2))
        (marksReferencePair p (pair.1 ++ pair.2))
        (fun query off => shared_programming_agrees compress p pair.1 query
          (shared_mark_left p pair.1 pair.2 query off).1)
        (fun query off => shared_programming_agrees compress p pair.2 query
          (shared_mark_left p pair.1 pair.2 query off).2) observer
      rw [measureTVDist_eq_toReal_measureETVDist] at step
      exact (ENNReal.toReal_le_toReal (measureETVDist_ne_top _ _)
        (ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ∞) (prEvent_le_one _))).mp step)
  rw [measureTVDist_eq_toReal_measureETVDist]
  apply ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) finite)
  apply bound.trans
  simpa only [flattened, map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind] using hit

end TwoPermutationPrototype.Sampling
