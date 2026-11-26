import CommitGolfCandidate.NonceChainPath
import CommitGolfCandidate.NonceChainHidden
import Mathlib.Data.List.FinRange

/-! A tape can be checked after any public forward/inverse strategy. Multiplying
by the number of possible tapes recovers the real-chain event probability when
the tape is averaged. -/
namespace CommitGolfCandidate.Permutation.CounterSalt
open NonceChain
open Finset
set_option linter.unusedSectionVars false
variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {n : Nat}

def edges (x y : Fin n → S) : List (S × S) :=
  List.ofFn fun i : Fin n => (x i, y i)

def follows (π : Equiv.Perm S) (x y : Fin n → S) : Prop := ∀ i, π (x i) = y i

def Bad (x y : Fin n → S) (t : Trace S) : Prop :=
  (∃ i, x i ∈ t.usedIn) ∨ Exposed y t.usedOut

theorem fresh_edges (x y : Fin n → S) (t : Trace S) (distinct : Function.Injective x)
    (safe : ¬Bad x y t) : Fresh (edges x y) t := by
  have inj : Function.Injective y := by
    intro i j eq
    by_contra diff
    exact safe (Or.inr ⟨i, Or.inr ⟨j, Ne.symm diff, eq⟩⟩)
  apply fresh_of_nodup
  · rw [edges, List.map_ofFn, List.nodup_ofFn]
    exact distinct
  · rw [edges, List.map_ofFn, List.nodup_ofFn]
    exact inj
  · intro e he hit
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact safe (Or.inl ⟨i,hit⟩)
  · intro e he hit
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact safe (Or.inr ⟨i,Or.inl hit⟩)

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

noncomputable def accept (b : Bool) := ind (b = true)

open Classical in
noncomputable def weight (g : Strat S Bool) (x y : Fin n → S) : ℝ :=
  mean fun π : Equiv.Perm S => if follows π x y then
    g.eager π PState.init (fun b _ => accept b) else 0

theorem weight_eq (g : Strat S Bool) (x y : Fin n → S) :
    weight g x y = g.exp PState.init (fun b st => if b then
      (checkEdges (edges x y)).prob st (fun b' _ => b' = true) else 0) := by
  classical
  let k : Bool → Strat S Bool := fun b => if b then checkEdges (edges x y) else .done false
  have eager (π : Equiv.Perm S) :
      (g.bind k).eager π PState.init (fun b _ => accept b) =
        if follows π x y then g.eager π PState.init (fun b _ => accept b) else 0 := by
    rw [eager_bind]
    have leaf (b : Bool) (st : PState S) :
        (k b).eager π st (fun b _ => accept b) =
        if follows π x y then accept b else 0 := by
      cases b
      · simp [k, Strat.eager, accept, ind]
      · simp only [k, ite_true, check_eager]
        have eq : (∀ e ∈ edges x y, π e.1 = e.2) ↔ follows π x y := by
          simp [edges,follows]
        by_cases good : follows π x y
        · rw [decide_eq_true (eq.mpr good), ite_eq_left good]
        · rw [decide_eq_false (fun h => good (eq.mp h)), ite_eq_right good]
          simp [accept,ind]
    simp only [leaf]
    by_cases good : follows π x y <;> simp [good,eager_zero]
  rw [weight, mean, avg_congr (fun π _ => (eager π).symm), Strat.avg_eager, Strat.exp_bind]
  apply congrArg (g.exp PState.init)
  funext b st
  cases b <;> simp [k,Strat.prob,accept,Strat.exp,ind]

theorem path_comparison (g : Strat S Bool) (x y : Fin n → S) (distinct : Function.Injective x) :
    g.exp PState.init (fun b _ => accept b) ≤
      (Fintype.card S : ℝ)^n * weight g x y +
        g.exp PState.init (fun _ st => ind (Bad x y st.trace)) := by
  classical
  rw [weight_eq, ← Strat.exp_mul_left, ← Strat.exp_add]
  apply Strat.exp_mono
  intro b st
  have pos : 0 < (Fintype.card S : ℝ) := by exact_mod_cast Fintype.card_pos
  have nonneg := (checkEdges (edges x y)).prob_nonneg st (fun b' _ => b' = true)
  cases b
  · simp [accept,ind_neg,ind_nonneg]
  · by_cases h : Bad x y st.trace
    · simp [accept, ind_pos h, ind_pos True.intro, mul_nonneg (pow_nonneg pos.le _) nonneg]
    · have prob := check_fresh (edges x y) st (fresh_edges x y st.trace distinct h)
      rw [show (edges x y).length = n by simp [edges], one_div_pow] at prob
      have one := (div_le_iff₀ (pow_pos pos n)).mp prob
      simpa [accept, ind_pos True.intro, ind_neg h, mul_comm] using one

end CommitGolfCandidate.Permutation.CounterSalt
