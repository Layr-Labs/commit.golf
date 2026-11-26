import CommitGolfCandidate.ReconstructedHidingReplay

namespace CommitGolfCandidate.Reconstruction.HidingReplay
open CommitGolfCandidate.Permutation CommitGolfCandidate.Permutation.NonceChain Finset
set_option linter.unusedSectionVars false
variable {S K D R : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype K] [Nonempty K] [Fintype D] [Nonempty D] [Fintype R] [Nonempty R] {n : Nat}

private theorem swap_means {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    mean (fun x => mean (f x)) = mean (fun y => mean (fun x => f x y)) := by
  rw [← mean_prod,← mean_prod]
  exact mean_equiv (Equiv.prodComm X Y) (fun p => f p.2 p.1)

def scheduled (x y : Fin n → S) : List (S × S) := List.ofFn fun i => (x i,y i)

theorem schedule_agrees (x y : Fin n → S) (π : Equiv.Perm S) :
    (∀ e ∈ scheduled x y, π e.1 = e.2) ↔ y = fun i => π (x i) := by
  simp only [scheduled,List.forall_mem_ofFn_iff]
  exact ⟨fun h => funext fun i => (h i).symm,fun h i => (congrFun h i).symm⟩

def publicBlocks (split : S ≃ D × R) (out : Fin n → S) : Fin n → D := fun i => (split (out i)).1

/-- Ideal public continuations receive the exposed part of every block. An eager
real continuation receives these parts evaluated by the same shared permutation. -/
noncomputable def realRun (split : S ≃ D × R) (address : K → Fin n → S)
    (g : (Fin n → D) → Strat S Bool) : ℝ :=
  mean fun π : Equiv.Perm S => mean fun k : K =>
    (g (publicBlocks split (fun i => π (address k i)))).eager π PState.init (fun b _ => accept b)

noncomputable def idealRun (g : (Fin n → D) → Strat S Bool) : ℝ :=
  mean fun d => (g d).exp PState.init (fun b _ => accept b)

/-- Averaging over independent proposed rows recovers the candidate's real rows
exactly once for each key and each permutation. -/
theorem schedule_weight (split : S ≃ D × R) (address : K → Fin n → S)
    (g : (Fin n → D) → Strat S Bool) :
    (Fintype.card S : ℝ)^n *
        mean (fun k : K => mean (fun y : Fin n → S =>
          rowWeight (g (publicBlocks split y)) (scheduled (address k) y))) =
      realRun split address g := by
  classical
  unfold realRun
  rw [swap_means (fun π k =>
    (g (publicBlocks split (fun i => π (address k i)))).eager π PState.init (fun b _ => accept b))]
  rw [← avg_mul_left]
  apply avg_congr
  intro k _
  unfold rowWeight
  rw [swap_means,← avg_mul_left]
  apply avg_congr
  intro π _
  simp_rw [schedule_agrees]
  unfold mean avg
  simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  rw [Finset.sum_ite_eq' univ]
  simp [field]

def tableSplit (split : S ≃ D × R) : (Fin n → S) ≃ ((Fin n → D) × (Fin n → R)) where
  toFun y := (publicBlocks split y,fun i => (split (y i)).2)
  invFun parts := fun i => split.symm (parts.1 i,parts.2 i)
  left_inv y := funext fun i => split.symm_apply_apply (y i)
  right_inv parts := Prod.ext
    (funext fun i => congrArg Prod.fst (split.apply_symm_apply (parts.1 i,parts.2 i)))
    (funext fun i => congrArg Prod.snd (split.apply_symm_apply (parts.1 i,parts.2 i)))

theorem split_average (split : S ≃ D × R) (f : (Fin n → S) → ℝ) :
    mean f = mean (fun d : Fin n → D => mean (fun r : Fin n → R =>
      f (fun i => split.symm (d i,r i)))) := by
  rw [← mean_prod]
  exact (mean_equiv (tableSplit split).symm f).symm

/-- This bounds the ideal-to-real discrepancy by the probability of an actual
input/output intersection or a repeated output, evaluated in the ideal run. -/
theorem compare_runs (split : S ≃ D × R) (address : K → Fin n → S)
    (g : (Fin n → D) → Strat S Bool) :
    idealRun g ≤ realRun split address g +
      mean (fun k : K => mean (fun y : Fin n → S =>
        (g (publicBlocks split y)).exp PState.init (fun _ st =>
          ind (¬ Fresh (scheduled (address k) y) st.trace)))) := by
  classical
  have ideal : idealRun g = mean (fun _ : K => mean (fun y : Fin n → S =>
      (g (publicBlocks split y)).exp PState.init (fun b _ => accept b))) := by
    have mconst {A : Type} [Fintype A] [Nonempty A] (v : ℝ) : mean (fun _ : A => v) = v :=
      avg_const Finset.univ_nonempty v
    rw [mconst,split_average split]
    have parts (d : Fin n → D) (r : Fin n → R) :
        publicBlocks split (fun i => split.symm (d i,r i)) = d :=
      funext fun i => congrArg Prod.fst (split.apply_symm_apply (d i,r i))
    simp_rw [parts]
    apply avg_congr
    intro d _
    exact (mconst _).symm
  rw [ideal,← schedule_weight split address g,← avg_mul_left,← avg_add]
  apply avg_mono
  intro k _
  rw [← avg_mul_left,← avg_add]
  apply avg_mono
  intro y _
  have h := row_comparison (g (publicBlocks split y)) (scheduled (address k) y)
  simpa only [scheduled,List.length_ofFn] using h

end CommitGolfCandidate.Reconstruction.HidingReplay
