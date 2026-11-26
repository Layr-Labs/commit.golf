import CommitGolfCandidate.LateFixed
import CommitGolfCandidate.LateArtifact

namespace CommitGolfCandidate.Late
open CommitGolf OracleComp

def transcript (s : Scheme) (m : Message) (p : Positions) :
    OracleComp World (Commitment × Proof) := do
  let (root, td) ← s.commit m
  let pf ← s.opening td p
  pure (root,pf)

def ViewRefinement : Prop :=
  ∀ o m p, view o (transcript submission.scheme m p) =
    view o (transcript (scheme submission.scheme.check) m p)

private theorem factor {S O : Type} {k : Nat} (s : Scheme) (a : Hiding.HidingAdversary S O k)
    (b : Bool) :
    Hiding.hidingExperiment s a b =
      (do let c ← a.choose
          let (root,pf) ← transcript s (if b then c.message₁ else c.message₀) c.positions
          a.observe c.aux root pf) := by
  simp only [Hiding.hidingExperiment, transcript, bind_assoc, pure_bind]

private theorem run_view {O : Type} (c : OracleComp World O) :
    Hiding.runHiding c = (Oracle.sample >>= fun o => view o c) := by
  simp only [Hiding.runHiding, view, map_eq_bind_pure_comp, Function.comp_def]

attribute [local irreducible] Artifact.submission Submission.scheme scheme transcript view

/-- Transport a proof of the model's single hiding goal to the exact machine
using equality of the joint commitment-and-opening view for each fixed oracle. -/
theorem machine_hiding (refines : ViewRefinement) (late_hiding : HidingGoal) :
    submission.scheme.Hiding HIDING_ERROR := by
  have hidden := late_hiding submission.scheme.check
  refine ⟨hidden.1, ?_⟩
  intro k t le S O adv bound
  have same (b : Bool) : Hiding.runHiding (Hiding.hidingExperiment submission.scheme adv b) =
      Hiding.runHiding (Hiding.hidingExperiment (scheme submission.scheme.check) adv b) := by
    rw [run_view, run_view]
    apply bind_congr
    intro o
    rw [factor, factor, view_bind, view_bind]
    apply bind_congr
    intro c
    rw [view_bind, view_bind, refines]
  rw [same false, same true]
  exact hidden.2 k t le S O adv bound

end CommitGolfCandidate.Late
