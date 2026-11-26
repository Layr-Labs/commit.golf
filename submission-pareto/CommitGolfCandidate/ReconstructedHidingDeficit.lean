import CommitGolfCandidate.ReconstructedHidingMarkedAlgebra

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolf OracleComp HidingTape TwoPermutationPrototype.Sampling CommitGolfCandidate.Permutation
open CommitGolfCandidate.Permutation.NonceChain (mean)
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000
local instance deficitDiscrete {α : Type} : MeasurableSpace α := ⊤

noncomputable def mass {A : Type} (d : ProbComp A) (ev : A → Prop) := (Pr{let a ← d}[ev a]).toReal

noncomputable def deficit {A : Type} (l r : ProbComp (A × Bool)) (ev : A → Prop) : ℝ :=
  1 - mass l (retained ev) - mass r (retained (fun a => ¬ev a))

theorem deficit_common {A : Type} (d l r : ProbComp (A × Bool)) (ev : A → Prop)
    (left : mass d (retained ev) ≤ mass l (retained ev))
    (right : mass d (retained (fun a => ¬ev a)) ≤ mass r (retained (fun a => ¬ev a))) :
    deficit l r ev ≤ mass d (fun a => a.2=false) := by
  classical
  let rep := Classical.choice (uniform_source d)
  let : Fintype rep.Seed := rep.finite
  let : Nonempty rep.Seed := rep.inhabited
  have split : mass d (fun a => a.2=false) + (mass d (retained ev) + mass d (retained (fun a => ¬ev a))) = 1 := by
    simp only [mass,rep.event,mean,←avg_add]
    trans avg Finset.univ (fun _ : rep.Seed => (1:ℝ))
    · apply avg_congr
      intro s _
      by_cases b : (rep.read s).2 = true <;> by_cases found : ev (rep.read s).1 <;>
        simp [ind,retained,b,found,Bool.eq_false_iff.mpr]
    · exact avg_const Finset.univ_nonempty _
  unfold deficit
  linarith

private theorem add_average {A : Type} [Fintype A] [Nonempty A] (f g h : A → ℝ) (e : ℝ)
    (point : ∀ a, 1 ≤ f a + (g a + (h a + e))) :
    1 - mean f - mean g ≤ mean h + e := by
  have take : mean (fun _ : A => (1:ℝ)) ≤ mean (fun a => f a + (g a + (h a + e))) :=
    avg_mono (fun a _ => point a)
  simp only [mean,avg_add,avg_const Finset.univ_nonempty] at take
  linarith

theorem deficit_bind {I A B : Type} (d : ProbComp I) (l r : I → ProbComp (A × Bool)) (ev : A → Prop)
    (bad : I → ProbComp B) (fail : B → Prop) (e : ℝ)
    (point : ∀ i ∈ support d, deficit (l i) (r i) ev ≤ mass (bad i) fail + e) :
    deficit (d >>= l) (d >>= r) ev ≤ mass (d >>= bad) fail + e := by
  classical
  let rep := Classical.choice (uniform_source d)
  let : Fintype rep.Seed := rep.finite
  let : Nonempty rep.Seed := rep.inhabited
  unfold deficit mass
  simp only [rep.bind_mean]
  apply add_average
  intro s
  have one := point (rep.read s) (rep.read_support s)
  unfold deficit mass at one
  linarith only [one]

theorem deficit_bind_const {I A : Type} (d : ProbComp I) (l r : I → ProbComp (A × Bool)) (ev : A → Prop)
    (e : ℝ) (point : ∀ i ∈ support d, deficit (l i) (r i) ev ≤ e) :
    deficit (d >>= l) (d >>= r) ev ≤ e := by
  let bad := fun _ : I => (pure false : ProbComp Bool)
  have inner (i : I) : mass (bad i) (·=true)=0 := by simp [mass,bad]
  have bound := deficit_bind d l r ev bad (·=true) e (fun i h => by rw [inner i,zero_add]; exact point i h)
  have z : mass (d >>= bad) (·=true)=0 := by
    have rep := Classical.choice (uniform_source d)
    change (Pr{let b ← (d >>= bad)}[b=true]).toReal=0
    rw [rep.bind_mean]
    exact (avg_congr (fun s _ => inner (rep.read s))).trans avg_zero
  rwa [z,zero_add] at bound

theorem mass_bind_zero {I A : Type} (d : ProbComp I) (f : I → ProbComp A) (ev : A → Prop)
    (point : ∀ i, mass (f i) ev=0) : mass (d >>= f) ev=0 := by
  let r := Classical.choice (uniform_source d)
  exact (r.bind_mean f ev).trans ((avg_congr (fun s _ => point (r.read s))).trans avg_zero)

theorem mass_bind_mono {I A : Type} (d : ProbComp I) (f g : I → ProbComp A) (ev : A → Prop)
    (point : ∀ i ∈ support d, mass (f i) ev ≤ mass (g i) ev) : mass (d >>= f) ev ≤ mass (d >>= g) ev := by
  let r := Classical.choice (uniform_source d)
  simp only [mass,r.bind_mean]
  exact avg_mono (fun s _ => point (r.read s) (r.read_support s))

end CommitGolfCandidate.Reconstruction.HidingTraffic
