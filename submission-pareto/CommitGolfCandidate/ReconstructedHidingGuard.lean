import CommitGolfCandidate.ReconstructedHidingIntegrate
import VCVio.EvalDist.MeasureTVDist.Event

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolf OracleComp CommitGolfCandidate.Permutation
open CommitGolfCandidate.Permutation.NonceChain (mean)
local instance guardDiscrete {α : Type} : MeasurableSpace α := ⊤
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

/-- Both sides can be replaced on the same exceptional seeds. The discrepancy
from the replacements is at most the probability of those seeds. -/
theorem shared_exception {S A : Type} (seed : ProbComp S) (bad : S → Prop)
    (actual guarded : Bool → S → ProbComp A)
    (clean : ∀ w s, ¬bad s → actual w s =ᵈ guarded w s)
    (common : ∀ s, bad s → guarded false s =ᵈ guarded true s) :
    measureTVDist (seed >>= actual false) (seed >>= actual true) ≤
      measureTVDist (seed >>= guarded false) (seed >>= guarded true) +
        (Pr{let s ← seed}[bad s]).toReal := by
  classical
  let rep := Classical.choice (uniform_source seed)
  let : Fintype rep.Seed := rep.finite
  have delta (w : Bool) (ev : A → Prop) :
      (Pr{let a ← (seed >>= actual w)}[ev a]).toReal +
        (Pr{let a ← (seed >>= guarded (!w))}[ev a]).toReal ≤
        (Pr{let a ← (seed >>= guarded w)}[ev a]).toReal +
        (Pr{let a ← (seed >>= actual (!w))}[ev a]).toReal + (Pr{let s ← seed}[bad s]).toReal := by
    simp only [rep.bind_mean,rep.event,mean,← avg_add]
    apply avg_mono
    intro k _
    let s := rep.read k
    by_cases h : bad s
    · rw [ind_pos h]
      have same : guarded (!w) s =ᵈ guarded w s := by cases w <;> first | exact common s h | exact (common s h).symm
      rw [same.prEvent_eq ev]
      have hi := ENNReal.toReal_mono ENNReal.one_ne_top (prEvent_le_one (ev <$> actual w s))
      have lo := ENNReal.toReal_nonneg (a := Pr{let a ← actual (!w) s}[ev a])
      simp only [ENNReal.toReal_one] at hi
      linarith
    · rw [ind_neg h,(clean w s h).prEvent_eq ev,(clean (!w) s h).prEvent_eq ev,add_zero]
  apply tv_le_of_events _ _ _ (add_nonneg (measureTVDist_nonneg _ _) ENNReal.toReal_nonneg)
  intro ev
  have old := abs_prEvent_toReal_sub_le_measureTVDist (seed >>= guarded false) (seed >>= guarded true) ev
    Measurable.of_discrete
  obtain ⟨lo,hi⟩ := abs_sub_le_iff.mp old
  have a := delta false ev
  have b := delta true ev
  simp only [Bool.not_false,Bool.not_true] at a b
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

end CommitGolfCandidate.Reconstruction.HidingTraffic
