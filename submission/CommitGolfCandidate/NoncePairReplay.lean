import CommitGolfCandidate.NonceChainPath
import CommitGolfCandidate.NonceChainHidden
import Mathlib.Data.List.FinRange

/-! Paired nonce expansion replay, generalized from `NonceChainReplay`.
The proposed input list and output list are conditioned separately: a reply may
also be the next input. Only within-role collisions or public exposure are bad.
No permutation-orbit assumption is made in this module. -/
namespace CommitGolfCandidate.Permutation.NoncePair
open NonceChain
open Finset
set_option linter.unusedSectionVars false
variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S] {n : Nat}

def edges (input output : Fin (n+1) → S) : List (S × S) :=
  List.ofFn fun i : Fin n => (input i.castSucc, output i.succ)

def follows (π : Equiv.Perm S) (input output : Fin (n+1) → S) : Prop :=
  ∀ i : Fin n, π (input i.castSucc) = output i.succ

def Bad (input output : Fin (n+1) → S) (t : Trace S) : Prop :=
  Exposed input t.usedIn ∨ Exposed output t.usedOut

/-- Inputs and outputs are fresh separately. Cross-role equality is permitted. -/
theorem fresh_edges (input output : Fin (n+1) → S) (t : Trace S)
    (safe : ¬Bad input output t) : Fresh (edges input output) t := by
  have left : ¬Exposed input t.usedIn := fun h => safe (Or.inl h)
  have right : ¬Exposed output t.usedOut := fun h => safe (Or.inr h)
  have inputInj : Function.Injective input := by
    intro i j eq
    by_contra diff
    exact left ⟨i, Or.inr ⟨j,Ne.symm diff,eq⟩⟩
  have outputInj : Function.Injective output := by
    intro i j eq
    by_contra diff
    exact right ⟨i, Or.inr ⟨j,Ne.symm diff,eq⟩⟩
  apply fresh_of_nodup
  · rw [edges, List.map_ofFn, List.nodup_ofFn]
    exact inputInj.comp (Fin.castSucc_injective n)
  · rw [edges, List.map_ofFn, List.nodup_ofFn]
    exact outputInj.comp (Fin.succ_injective n)
  · intro e he hi
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact left ⟨_, Or.inl hi⟩
  · intro e he ho
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    exact right ⟨_, Or.inl ho⟩

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
noncomputable def weight (g : Strat S Bool) (input output : Fin (n+1) → S) : ℝ :=
  mean fun π : Equiv.Perm S => if follows π input output then
    g.eager π PState.init (fun b _ => accept b) else 0

theorem weight_eq (g : Strat S Bool) (input output : Fin (n+1) → S) :
    weight g input output = g.exp PState.init (fun b st => if b then
      (checkEdges (edges input output)).prob st (fun b' _ => b' = true) else 0) := by
  classical
  let k : Bool → Strat S Bool := fun b => if b then checkEdges (edges input output) else .done false
  have eager (π : Equiv.Perm S) :
      (g.bind k).eager π PState.init (fun b _ => accept b) =
        if follows π input output then g.eager π PState.init (fun b _ => accept b) else 0 := by
    rw [eager_bind]
    have leaf (b : Bool) (st : PState S) :
        (k b).eager π st (fun b _ => accept b) =
        if follows π input output then accept b else 0 := by
      cases b
      · simp [k, Strat.eager, accept, ind]
      · simp only [k, if_true, check_eager]
        have eq : (∀ e ∈ edges input output, π e.1 = e.2) ↔ follows π input output := by
          simp [edges, List.forall_mem_ofFn_iff,follows]
        by_cases good : follows π input output
        · rw [decide_eq_true (eq.mpr good), if_pos good]
        · rw [decide_eq_false (fun h => good (eq.mp h)), if_neg good]
          simp [accept,ind]
    simp only [leaf]
    by_cases good : follows π input output <;> simp [good,eager_zero]
  rw [weight, mean, avg_congr (fun π _ => (eager π).symm), Strat.avg_eager, Strat.exp_bind]
  apply congrArg (g.exp PState.init)
  funext b st
  cases b <;> simp [k,Strat.prob,accept,Strat.exp,ind]

theorem path_comparison (g : Strat S Bool) (input output : Fin (n+1) → S) :
    g.exp PState.init (fun b _ => accept b) ≤
      (Fintype.card S : ℝ)^n * weight g input output +
        g.exp PState.init (fun _ st => ind (Bad input output st.trace)) := by
  classical
  rw [weight_eq, ← Strat.exp_mul_left, ← Strat.exp_add]
  apply Strat.exp_mono
  intro b st
  have pos : 0 < (Fintype.card S : ℝ) := by exact_mod_cast Fintype.card_pos
  have nonneg := (checkEdges (edges input output)).prob_nonneg st (fun b' _ => b' = true)
  cases b
  · simp [accept,ind_neg,ind_nonneg]
  · by_cases h : Bad input output st.trace
    · simp [accept, ind_pos h, ind_pos True.intro, mul_nonneg (pow_nonneg pos.le _) nonneg]
    · have prob := check_fresh (edges input output) st (fresh_edges input output st.trace h)
      rw [show (edges input output).length = n by simp [edges], one_div_pow] at prob
      have one := (div_le_iff₀ (pow_pos pos n)).mp prob
      simpa [accept, ind_pos True.intro, ind_neg h, mul_comm] using one

end CommitGolfCandidate.Permutation.NoncePair
