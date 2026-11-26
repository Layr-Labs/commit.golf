import CommitGolfCandidate.ReconstructedHidingTrack

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolf OracleComp CommitGolfCandidate.Permutation HidingTape
open CommitGolfCandidate.Permutation.NonceChain (accept)
set_option maxRecDepth 12000
set_option maxHeartbeats 1400000
set_option exponentiation.threshold 2048

theorem checked_query {A : Type} (allow : Reply → Reply → Bool) (q : World.Domain)
    (next : World.Range q → OracleComp World A) (flag : Bool) :
    checkedQueries allow ((liftM (World.query q) : OracleComp World _) >>= next) flag =
      ((liftM (World.query q) : OracleComp World _) >>= fun a => checkedQueries allow (next a) (flag && allowAnswer allow q a)) := rfl

theorem spoiled_eager {A : Type} (allow : Reply → Reply → Bool) (c : Compression) (π : Perm)
    (g : OracleComp World A) (s : PState Reply) (score : A × Bool → ℝ) (constant : ℝ)
    (after : ∀ a, score (a,false)=constant) :
    (toStrat c (checkedQueries allow g false)).eager π s (fun a _ => score a) = constant := by
  induction g using OracleComp.inductionOn generalizing s with
  | pure a => exact after a
  | query_bind q next ih =>
    rw [checked_query]
    rcases q with coins | inp | x | y
    · rw [to_strat_coins]
      exact (avg_congr (fun a _ => ih a s)).trans (avg_const Finset.univ_nonempty constant)
    · rw [to_strat_compress]
      exact ih _ s
    · rw [to_strat_permute]
      exact ih _ _
    · rw [to_strat_inverse]
      exact ih _ _

/-- On every retained reference path, the second oracle gives the same answers
and the second permission test keeps that path. -/
theorem marked_lower {A : Type} (origin allowed : Reply → Reply → Bool) (c : Compression) (π ρ : Perm)
    (agree : ∀ x, origin x (π x)=true → ρ x=π x ∧ allowed x (π x)=true)
    (g : OracleComp World A) (s : PState Reply) (ev : A → Prop) :
    (toStrat c (checkedQueries origin g true)).eager π s (fun v _ => ind (ev v.1 ∧ v.2=true)) ≤
      (toStrat c (checkedQueries allowed g true)).eager ρ s (fun v _ => ind (ev v.1 ∧ v.2=true)) := by
  let score (v : A × Bool) := ind (ev v.1 ∧ v.2=true)
  have zero (a : A) : score (a,false)=0 := by exact ind_neg (by simp)
  induction g using OracleComp.inductionOn generalizing s with
  | pure a => exact le_rfl
  | query_bind q next ih =>
    rw [checked_query,checked_query]
    rcases q with coins | inp | x | y
    · rw [to_strat_coins,to_strat_coins]
      exact avg_mono (fun a _ => ih a s)
    · rw [to_strat_compress,to_strat_compress]
      exact ih _ s
    · rw [to_strat_permute,to_strat_permute]
      simp only [Strat.eager,allowAnswer,Bool.true_and]
      cases h : origin x (π x) with
      | false =>
        exact (spoiled_eager origin c π _ _ score 0 zero).le.trans (Strat.eager_nonneg ρ (fun _ _ => ind_nonneg _) _ _)
      | true =>
        obtain ⟨same,good⟩ := agree x h
        rw [same,good]
        exact ih _ _
    · rw [to_strat_inverse,to_strat_inverse]
      simp only [Strat.eager,allowAnswer,Bool.true_and]
      cases h : origin (π.symm y) y with
      | false =>
        exact (spoiled_eager origin c π _ _ score 0 zero).le.trans (Strat.eager_nonneg ρ (fun _ _ => ind_nonneg _) _ _)
      | true =>
        obtain ⟨same,good⟩ := agree (π.symm y) (by simpa only [Equiv.apply_symm_apply] using h)
        rw [Equiv.apply_symm_apply] at same good
        have inverse : ρ.symm y=π.symm y := ρ.symm_apply_eq.mpr same.symm
        rw [inverse,good]
        exact ih _ _

open Classical in
noncomputable def permitSets {K : Type} (ins outs : K → Finset Reply) (k : K) (x y : Reply) : Bool :=
  decide (¬touches ins outs k x y)

/-- The complement of the reference flag is precisely the first-hit process
whose adaptive cost is bounded by the chosen and random query ends. -/
theorem marked_failure {K A : Type} (ins outs : K → Finset Reply) (k : K) (c : Compression) (π : Perm)
    (g : OracleComp World A) (s : PState Reply) :
    (toStrat c (checkedQueries (permitSets ins outs k) g true)).eager π s (fun v _ => ind (v.2=false)) =
      (stopOnHit ins outs k (toStrat c g)).eager π s (fun b _ => accept b) := by
  classical
  let allow := permitSets ins outs k
  let score (v : A × Bool) := ind (v.2=false)
  have hit (a : A) : score (a,false)=1 := ind_pos rfl
  induction g using OracleComp.inductionOn generalizing s with
  | pure a => exact ind_neg (by decide : ¬true=false) |>.trans (ind_neg (by decide : ¬(false=true))).symm
  | query_bind q next ih =>
    rw [checked_query]
    rcases q with coins | inp | x | y
    · rw [to_strat_coins,to_strat_coins]
      exact avg_congr (fun a _ => ih a s)
    · rw [to_strat_compress,to_strat_compress]
      exact ih _ s
    · rw [to_strat_permute,to_strat_permute]
      simp only [Strat.eager,stopOnHit,allowAnswer,Bool.true_and]
      by_cases bad : touches ins outs k x (π x)
      · rw [ite_eq_left bad]
        simp only [permitSets,bad,not_true_eq_false,decide_false,Strat.eager]
        exact (spoiled_eager allow c π _ _ score 1 hit).trans (ind_pos (by decide : true=true)).symm
      · rw [ite_eq_right bad]
        rw [show permitSets ins outs k x (π x)=true from decide_eq_true bad]
        exact ih (π x) _
    · rw [to_strat_inverse,to_strat_inverse]
      simp only [Strat.eager,stopOnHit,allowAnswer,Bool.true_and]
      by_cases bad : touches ins outs k (π.symm y) y
      · rw [ite_eq_left bad]
        simp only [permitSets,bad,not_true_eq_false,decide_false,Strat.eager]
        exact (spoiled_eager allow c π _ _ score 1 hit).trans (ind_pos (by decide : true=true)).symm
      · rw [ite_eq_right bad]
        rw [show permitSets ins outs k (π.symm y) y=true from decide_eq_true bad]
        exact ih (π.symm y) _

end CommitGolfCandidate.Reconstruction.HidingTraffic
