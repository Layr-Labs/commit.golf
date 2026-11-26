import CommitGolfCandidate.ReconstructedHidingMarkedPosterior
import CommitGolfCandidate.ReconstructedHidingBaseGate

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolf OracleComp HidingTape TwoPermutationPrototype.Sampling CommitGolfCandidate.Permutation
open CommitGolfCandidate.Permutation.NonceChain (mean)
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
set_option exponentiation.threshold 2048
attribute [local irreducible] checkedQueries
local instance algebraDiscrete {α : Type} : MeasurableSpace α := ⊤

def retained {A : Type} (ev : A → Prop) (v : A × Bool) := ev v.1 ∧ v.2=true

theorem checked_initial {A : Type} (allow : Reply → Reply → Bool) (g : OracleComp World A) (a b : Bool) :
    checkedQueries allow g (a && b) = (fun v => (v.1,a && v.2)) <$> checkedQueries allow g b := by
  induction g using OracleComp.inductionOn generalizing b with
  | pure x => rw [checked_pure,checked_pure,map_pure]
  | query_bind q next ih =>
    rw [checked_query,checked_query,map_bind]
    apply bind_congr
    intro v
    rw [Bool.and_assoc]
    exact ih v _

theorem checked_closed_zero {A : Type} (o : Oracle) (allow : Reply → Reply → Bool)
    (g : OracleComp World A) (ev : A → Prop) :
    Pr{let v ← fixedOracleRun o (checkedQueries allow g false)}[retained ev v]=0 := by
  have shape := checked_initial allow g false true
  rw [show (false && true)=false from rfl] at shape
  rw [shape,fixed_oracle_run_map,prEvent_map]
  exact prEvent_eq_zero_of_forall_mem_support _ _ (fun _ _ h => Bool.noConfusion h.2)

theorem real_bind_add {A B : Type} (d : ProbComp A) (f g : A → ProbComp B) (ev : B → Prop) (e : ℝ)
    (pointwise : ∀ a ∈ support d, (Pr{let v ← f a}[ev v]).toReal ≤ (Pr{let v ← g a}[ev v]).toReal + e) :
    (Pr{let v ← (d >>= f)}[ev v]).toReal ≤ (Pr{let v ← (d >>= g)}[ev v]).toReal + e := by
  classical
  let r := Classical.choice (uniform_source d)
  let : Fintype r.Seed := r.finite
  let : Nonempty r.Seed := r.inhabited
  rw [r.bind_mean,r.bind_mean,mean,←avg_const (Finset.univ_nonempty (α := r.Seed)) e,←avg_add]
  exact avg_mono (fun s _ => pointwise (r.read s) (r.read_support s))

theorem real_bind_mark {A B : Type} (d : ProbComp A) (f g : A → ProbComp B) (ev : B → Prop) (bad : A → Prop)
    (clean : ∀ a ∈ support d, ¬bad a → (Pr{let v ← f a}[ev v]).toReal ≤ (Pr{let v ← g a}[ev v]).toReal) :
    (Pr{let v ← (d >>= f)}[ev v]).toReal ≤ (Pr{let v ← (d >>= g)}[ev v]).toReal + (Pr{let a ← d}[bad a]).toReal := by
  classical
  let r := Classical.choice (uniform_source d)
  let : Fintype r.Seed := r.finite
  simp only [r.bind_mean,r.event,mean,←avg_add]
  apply avg_mono
  intro s _
  by_cases failed : bad (r.read s)
  · rw [ind_pos failed]
    have one := ENNReal.toReal_mono ENNReal.one_ne_top (prEvent_le_one (ev <$> f (r.read s)))
    have zero := ENNReal.toReal_nonneg (a := Pr{let v ← g (r.read s)}[ev v])
    rw [ENNReal.toReal_one] at one
    linarith
  · rw [ind_neg failed,add_zero]
    exact clean (r.read s) (r.read_support s) failed

end CommitGolfCandidate.Reconstruction.HidingTraffic
