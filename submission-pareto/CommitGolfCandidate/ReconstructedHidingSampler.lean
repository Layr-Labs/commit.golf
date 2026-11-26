import CommitGolfCandidate.ReconstructedHidingAdaptiveWorlds

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolf OracleComp OracleSpec CommitGolfCandidate.Permutation CommitGolfCandidate.Permutation.NonceChain
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
local instance samplerDiscrete {α : Type} : MeasurableSpace α := ⊤

structure UniformSource {A : Type} (sample : ProbComp A) where
  Seed : Type
  finite : Fintype Seed
  inhabited : Nonempty Seed
  read : Seed → A
  event (e : A → Prop) :
    (Pr{let a ← sample}[e a]).toReal = @mean Seed finite (fun seed => ind (e (read seed)))

private theorem branch_mean {A : Type} (n : Nat) (next : Fin (n+1) → ProbComp A) (e : A → Prop) :
    (Pr{let a ← ($[0..n] >>= next)}[e a]).toReal =
      mean (fun i => (Pr{let a ← next i}[e a]).toReal) := by
  classical
  have mass (i : Fin (n+1)) : Pr{let x ← $[0..n]}[x = i] = (Fintype.card (Fin (n+1)) : ENNReal)⁻¹ := by
    have count := prEvent_liftM_query_eq_card_div (spec := unifSpec) n (fun x : Fin (n+1) => x=i)
    simpa [ProbComp.uniformFin_def,Finset.filter_eq'] using count
  have nonneg (i : Fin (n+1)) : 0 ≤ (Pr{let a ← next i}[e a]).toReal := ENNReal.toReal_nonneg
  have eq : Pr{let a ← ($[0..n] >>= next)}[e a] =
      ENNReal.ofReal (mean (fun i => (Pr{let a ← next i}[e a]).toReal)) := by
    rw [prEvent_bind_eq_sum_fintype,← sum_inv_card_mul_ofReal _ nonneg]
    apply Finset.sum_congr rfl
    intro i _
    rw [mass,ENNReal.ofReal_toReal (prEvent_ne_top _)]
  rw [eq,ENNReal.toReal_ofReal (avg_nonneg (fun i _ => nonneg i))]

private theorem coordinate_mean {I : Type} [Fintype I] [DecidableEq I] (B : I → Type)
    [∀ i, Fintype (B i)] [∀ i, Nonempty (B i)] (i : I) (f : B i → ℝ) :
    mean (fun s : ∀ j, B j => f (s i)) = mean f := by
  let split := Equiv.piSplitAt i B
  have h := mean_equiv split (fun p => f p.1)
  change mean (fun s : ∀ j, B j => f (s i)) = _ at h
  rw [h,mean_prod (fun a (_ : ∀ j : {j : I // j ≠ i}, B j) => f a)]
  simp only [mean,avg_const Finset.univ_nonempty]

/-- Every contest probability program uses finite-range coins. Its entire
output distribution can be represented as a function of one finite uniform
seed, even when the sizes of later draws depend on earlier results. -/
theorem uniform_source {A : Type} (p : ProbComp A) : Nonempty (UniformSource p) := by
  classical
  induction p using ProbComp.inductionOn with
  | pure a =>
    refine ⟨⟨Unit,inferInstance,inferInstance,fun _ => a,?_⟩⟩
    intro e
    rw [prEvent_pure,mean,avg_const Finset.univ_nonempty]
    by_cases h : e a <;> simp [h,ind]
  | query_bind n next ih =>
    let rep := fun i => Classical.choice (ih i)
    let B := fun i => (rep i).Seed
    let finite (i : Fin (n+1)) : Fintype (B i) := (rep i).finite
    let inhabited (i : Fin (n+1)) : Nonempty (B i) := (rep i).inhabited
    let Seed := Fin (n+1) × (∀ j, B j)
    let read := fun s : Seed => (rep s.1).read (s.2 s.1)
    refine ⟨⟨Seed,inferInstance,inferInstance,read,?_⟩⟩
    intro e
    rw [branch_mean]
    change _ = mean (fun s : Fin (n+1) × (∀ j,B j) => ind (e ((rep s.1).read (s.2 s.1))))
    rw [mean_prod (fun (i : Fin (n+1)) (s : ∀ j, B j) => ind (e ((rep i).read (s i))))]
    apply avg_congr
    intro i _
    exact ((rep i).event e).trans (coordinate_mean B i (fun v => ind (e ((rep i).read v)))).symm

end CommitGolfCandidate.Reconstruction.HidingTraffic
