import CommitGolfCandidate.SharedPinnedCacheCap

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
open scoped ENNReal
local instance SharedPinnedPairCouplingDiscrete {α : Type} : MeasurableSpace α := ⊤

theorem shared_product_reference_hit {α : Type} (left right : ProbComp (List Row))
    (compress : Compression) (p : BiPermutation Block) (observer : OracleComp World α) :
    measureETVDist
      (left >>= fun rows => fixedOracleRun (fixedOracle compress (p.programRows rows)) observer)
      (right >>= fun rows => fixedOracleRun (fixedOracle compress (p.programRows rows)) observer) ≤
      Pr{let result ← (do
        let l ← left
        let r ← right
        flaggedRun (fixedOracle compress p) (marksReferencePair p (l ++ r)) observer)}[
          result.2.2 = true] := by
  let joint : ProbComp (List Row × List Row) := do
    let l ← left
    let r ← right
    pure (l,r)
  let run (rows : List Row) := fixedOracleRun (fixedOracle compress (p.programRows rows)) observer
  have leftEq : (left >>= run) =ᵈ (joint >>= fun pair => run pair.1) := by
    unfold joint
    simp only [bind_assoc, pure_bind]
    apply EvalDistEq.bind_right
    intro l
    exact (EvalDistEq.of_evalDist_eq (evalDist_bind_const right (run l))).symm
  have rightEq : (right >>= run) =ᵈ (joint >>= fun pair => run pair.2) := by
    unfold joint
    simp only [bind_assoc, pure_bind]
    exact (EvalDistEq.of_evalDist_eq (evalDist_bind_const left (right >>= run))).symm
  change measureETVDist (left >>= run) (right >>= run) ≤ _
  unfold measureETVDist
  rw [leftEq.evalDist_eq, rightEq.evalDist_eq]
  change measureETVDist (joint >>= fun pair => run pair.1) (joint >>= fun pair => run pair.2) ≤ _
  have bound := distance_averaged_event joint
    (fun pair => run pair.1) (fun pair => run pair.2)
    (fun pair => flaggedRun (fixedOracle compress p) (marksReferencePair p (pair.1 ++ pair.2)) observer)
    (fun result => result.2.2 = true)
    (fun pair => shared_pair_reference_hit compress p pair.1 pair.2 observer)
  simpa only [joint, bind_assoc, pure_bind] using bound

theorem shared_reference_initial_true {α : Type} (compress : Compression) (p : BiPermutation Block)
    (rows : List Row) (observer : OracleComp World α) :
    Pr{let result ← flaggedRun (fixedOracle compress p) (marksReferencePair p rows) observer true}[
      result.2.2 = true] = 1 := by
  rw [flagged_reference_trace]
  simp only [prEvent_map, Bool.true_or]
  exact prEvent_eq_one_of_forall_mem_support _ _ (fun _ _ => True.intro)

end TwoPermutationPrototype.Sampling
