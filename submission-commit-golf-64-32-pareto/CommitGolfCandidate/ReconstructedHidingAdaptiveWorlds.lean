import CommitGolfCandidate.ReconstructedHidingAdaptiveHit

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolfCandidate.Permutation CommitGolfCandidate.Permutation.NonceChain Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable {S K A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype K] [Nonempty K]

open Classical in
noncomputable def stopOnHit (ins outs : K → Finset S) (k : K) : Strat S A → Strat S Bool
  | .done _ => .done false
  | .rand m next => .rand m fun i => stopOnHit ins outs k (next i)
  | .fwd x next => .fwd x fun y => if touches ins outs k x y then .done true else stopOnHit ins outs k (next y)
  | .inv y next => .inv y fun x => if touches ins outs k x y then .done true else stopOnHit ins outs k (next x)

theorem stop_exp (ins outs : K → Finset S) (k : K) (g : Strat S A) (s : PState S) :
    (stopOnHit ins outs k g).exp s (fun b _ => accept b) = hitProb ins outs k g s.trace := by
  classical
  induction g generalizing s with
  | done _ => simp [stopOnHit,Strat.exp,hitProb,accept,ind]
  | rand _ _ ih => exact avg_congr (fun i _ => ih i s)
  | fwd x next ih =>
    apply avg_congr
    intro y _
    by_cases h : touches ins outs k x y
    · simp [h,Strat.exp,accept,ind]
    · simpa only [ite_eq_right h] using ih y ⟨s.trace.stepF x y,s.count+1⟩
  | inv y next ih =>
    apply avg_congr
    intro x _
    by_cases h : touches ins outs k x y
    · simp [h,Strat.exp,accept,ind]
    · simpa only [ite_eq_right h] using ih x ⟨s.trace.stepI x y,s.count+1⟩

private theorem eager_le_one (g : Strat S A) (π : Equiv.Perm S) (s : PState S) (ev : A → Prop) :
    g.eager π s (fun a _ => ind (ev a)) ≤ 1 := by
  induction g generalizing s with
  | done _ => exact ind_le_one _
  | rand _ _ ih => exact avg_le zero_le_one (fun i _ => ih i s)
  | fwd _ _ ih => exact ih _ _
  | inv _ _ ih => exact ih _ _

theorem eager_worlds (ins outs : K → Finset S) (k : K) (p l r : Equiv.Perm S)
    (consistent : ∀ x, ¬touches ins outs k x (p x) → l x = p x ∧ r x = p x)
    (g : Strat S A) (s : PState S) (ev : A → Prop) :
    g.eager l s (fun a _ => ind (ev a)) ≤ g.eager r s (fun a _ => ind (ev a)) +
      (stopOnHit ins outs k g).eager p s (fun b _ => accept b) := by
  classical
  induction g generalizing s with
  | done a => simp [Strat.eager,stopOnHit,accept,ind]
  | rand m next ih =>
    simp only [stopOnHit,Strat.eager,←avg_add]
    exact avg_mono (fun i _ => ih i s)
  | fwd x next ih =>
    simp only [stopOnHit,Strat.eager]
    by_cases hit : touches ins outs k x (p x)
    · rw [ite_eq_left hit]
      simp only [Strat.eager,accept,ind_pos True.intro]
      have lo := (next (r x)).eager_nonneg r (fun a _ => ind_nonneg (ev a)) ⟨s.trace.stepF x (r x),s.count+1⟩
      exact (eager_le_one (next (l x)) l _ ev).trans (le_add_of_nonneg_left lo)
    · obtain ⟨a,b⟩ := consistent x hit
      rw [ite_eq_right hit,a,b]
      exact ih (p x) _
  | inv y next ih =>
    simp only [stopOnHit,Strat.eager]
    by_cases hit : touches ins outs k (p.symm y) y
    · rw [ite_eq_left hit]
      simp only [Strat.eager,accept,ind_pos True.intro]
      have lo := (next (r.symm y)).eager_nonneg r (fun a _ => ind_nonneg (ev a)) ⟨s.trace.stepI (r.symm y) y,s.count+1⟩
      exact (eager_le_one (next (l.symm y)) l _ ev).trans (le_add_of_nonneg_left lo)
    · obtain ⟨a,b⟩ := consistent (p.symm y) (by simpa using hit)
      have la : l.symm y = p.symm y := l.symm_apply_eq.mpr (by simpa using a.symm)
      have rb : r.symm y = p.symm y := r.symm_apply_eq.mpr (by simpa using b.symm)
      rw [ite_eq_right hit,la,rb]
      exact ih (p.symm y) _

/-- The two compared permutations may vary with the same hidden randomness.
Averaging over a uniform completion of the initial table turns their event
discrepancy into the chance of an actual hit on one reference transcript. -/
theorem completion_worlds (base : Trace S) (well : base.WF) (inhabited : base.ext.Nonempty)
    (ins outs : K → Finset S) (l r : K → Equiv.Perm S → Equiv.Perm S)
    (agrees : ∀ k, ∀ p ∈ base.ext, ∀ x, ¬touches ins outs k x (p x) →
      l k p x = p x ∧ r k p x = p x) (g : Strat S A) (ev : A → Prop) :
    let s : PState S := ⟨base,base.length⟩
    mean (fun k => avg base.ext (fun p => g.eager (l k p) s (fun a _ => ind (ev a)))) ≤
      mean (fun k => avg base.ext (fun p => g.eager (r k p) s (fun a _ => ind (ev a)))) +
        mean (fun k => hitProb ins outs k g base) := by
  let s : PState S := ⟨base,base.length⟩
  dsimp only
  rw [←avg_add]
  apply avg_mono
  intro k _
  have changed := avg_mono (fun p hp => eager_worlds ins outs k p (l k p) (r k p) (agrees k p hp) g s ev)
  rw [avg_add] at changed
  apply changed.trans_eq
  apply congrArg (fun z : ℝ => avg base.ext (fun p => g.eager (r k p) s (fun a _ => ind (ev a))) + z)
  change avg base.ext (fun p => (stopOnHit ins outs k g).eager p s (fun b _ => accept b)) = _
  unfold avg
  rw [(stopOnHit ins outs k g).sum_eager s well _]
  have nonzero : (base.ext.card:ℝ) ≠ 0 := by exact_mod_cast inhabited.card_ne_zero
  change (base.ext.card:ℝ) * (stopOnHit ins outs k g).exp s _ / base.ext.card = _
  rw [mul_div_cancel_left₀ _ nonzero,stop_exp]

end CommitGolfCandidate.Reconstruction.HidingTraffic
