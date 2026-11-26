import CommitGolfCandidate.NonceChainReplay

/-! Conditioning a public permutation computation on an arbitrary list of rows,
including the repaired generator's separately addressed blocks. -/
namespace CommitGolfCandidate.Reconstruction.HidingReplay
open CommitGolfCandidate.Permutation CommitGolfCandidate.Permutation.NonceChain
open Finset
set_option linter.unusedSectionVars false
variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

private theorem eager_bind {A D : Type} (π : Equiv.Perm S) (g : Strat S A)
    (k : A → Strat S D) (s : PState S) (f : D → PState S → ℝ) :
    (g.bind k).eager π s f = g.eager π s (fun a s' => (k a).eager π s' f) := by
  induction g generalizing s with
  | done => rfl
  | fwd x k ih => exact ih _ _
  | inv y k ih => exact ih _ _
  | rand m k ih => exact avg_congr fun i _ => ih i _

private theorem eager_zero {A : Type} (π : Equiv.Perm S) (g : Strat S A) (s : PState S) :
    g.eager π s (fun _ _ => 0) = 0 := by
  induction g generalizing s with
  | done => rfl
  | fwd x k ih => exact ih _ _
  | inv y k ih => exact ih _ _
  | rand m k ih => simp [Strat.eager, ih, avg_zero]

open Classical in
noncomputable def rowWeight (g : Strat S Bool) (rows : List (S × S)) : ℝ :=
  mean fun π : Equiv.Perm S => if ∀ e ∈ rows, π e.1 = e.2 then
    g.eager π PState.init (fun b _ => accept b) else 0

/-- The likelihood of a particular keyed set of rows can be checked after the
public adaptive strategy, preserving its forward and inverse answers. -/
theorem rowWeight_eq (g : Strat S Bool) (rows : List (S × S)) :
    rowWeight g rows = g.exp PState.init (fun b st => if b then
      (checkEdges rows).prob st (fun b' _ => b' = true) else 0) := by
  classical
  let k : Bool → Strat S Bool := fun b => if b then checkEdges rows else .done false
  have eager (π : Equiv.Perm S) :
      (g.bind k).eager π PState.init (fun b _ => accept b) =
        if ∀ e ∈ rows, π e.1 = e.2 then g.eager π PState.init (fun b _ => accept b) else 0 := by
    rw [eager_bind]
    have leaf (b : Bool) (st : PState S) :
        (k b).eager π st (fun b _ => accept b) =
        if ∀ e ∈ rows, π e.1 = e.2 then accept b else 0 := by
      cases b
      · simp [k, Strat.eager, accept, ind]
      · simp only [k, ite_true, check_eager]
        by_cases good : ∀ e ∈ rows, π e.1 = e.2 <;> simp [good, accept,ind]
    simp only [leaf]
    by_cases good : ∀ e ∈ rows, π e.1 = e.2
    · simp only [if_pos good]
    · simp only [if_neg good,eager_zero]
  rw [rowWeight, mean, avg_congr (fun π _ => (eager π).symm), Strat.avg_eager, Strat.exp_bind]
  apply congrArg (g.exp PState.init)
  funext b st
  cases b <;> simp [k,Strat.prob,accept,Strat.exp,ind]

theorem row_comparison (g : Strat S Bool) (rows : List (S × S)) :
    g.exp PState.init (fun b _ => accept b) ≤
      (Fintype.card S : ℝ)^rows.length * rowWeight g rows +
      g.exp PState.init (fun _ st => ind (¬ Fresh rows st.trace)) := by
  classical
  rw [rowWeight_eq, ← Strat.exp_mul_left, ← Strat.exp_add]
  apply Strat.exp_mono
  intro b st
  have positive : 0 < (Fintype.card S : ℝ) := by exact_mod_cast Fintype.card_pos
  have nonneg := (checkEdges rows).prob_nonneg st (fun b' _ => b' = true)
  cases b
  · simp [accept,ind_neg,ind_nonneg]
  · by_cases fresh : Fresh rows st.trace
    · have likelihood := check_fresh rows st fresh
      rw [one_div_pow] at likelihood
      have one := (div_le_iff₀ (pow_pos positive rows.length)).mp likelihood
      simpa [accept,ind, fresh,mul_comm] using one
    · simp [accept,ind_pos fresh,
        ind_pos True.intro, mul_nonneg (pow_nonneg positive.le _) nonneg]

/-- The input/output lists can be distinct: unlike an orbit, a keyed schedule has
one independent designated input and one reply per row. -/
theorem scheduled_fresh {n : Nat} (inputs outputs : Fin n → S) (st : Trace S)
    (inDistinct : Function.Injective inputs) (outDistinct : Function.Injective outputs)
    (inFresh : ∀ i, inputs i ∉ st.usedIn) (outFresh : ∀ i, outputs i ∉ st.usedOut) :
    Fresh (List.ofFn fun i => (inputs i, outputs i)) st := by
  apply fresh_of_nodup
  · rw [List.map_ofFn,List.nodup_ofFn]; exact inDistinct
  · rw [List.map_ofFn,List.nodup_ofFn]; exact outDistinct
  · intro e mem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    exact inFresh i
  · intro e mem
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp mem
    exact outFresh i

end CommitGolfCandidate.Reconstruction.HidingReplay
