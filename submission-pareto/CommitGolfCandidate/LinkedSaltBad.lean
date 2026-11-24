import CommitGolfCandidate.LinkedSaltSchedule

/-! The per-step bound of the linked hybrid. Every keyed input is injective in the private key and
every proposed reply is injective in its own hidden part, so a run of at most `q` queries meets the
bad event with probability at most `n (3q + 2n) / |K|` over the key and the hidden parts. -/
namespace CommitGolfCandidate.Permutation.LinkedSalt
open Finset NonceChain
set_option linter.unusedSectionVars false
variable {S K : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype K] [Nonempty K] {n : Nat}

theorem mean_swap {A B : Type} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    mean (fun a => mean (f a)) = mean (fun b => mean (fun a => f a b)) := by
  rw [← mean_prod, ← mean_prod]
  exact mean_equiv (Equiv.prodComm ..) (fun p : B × A => f p.2 p.1)

theorem exp_mean {A T : Type} [Fintype A] (g : Strat S T) (s : PState S)
    (f : A → T → PState S → ℝ) :
    mean (fun a => g.exp s (f a)) = g.exp s (fun b st => mean (fun a => f a b st)) := by
  unfold mean avg
  simp_rw [div_eq_inv_mul, ← Strat.exp_sum, ← Strat.exp_mul_left]

private theorem key_hit (e : K → S) (inj : Function.Injective e) (seen : Finset S) :
    mean (fun k => ind (e k ∈ seen)) ≤ seen.card / (Fintype.card K : ℝ) := by
  classical
  unfold mean avg
  rw [sum_ind, Finset.card_univ]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  norm_cast
  apply Finset.card_le_card_of_injOn e _ inj.injOn
  intro k hk
  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  exact hk

private theorem input_hits (x : Fin n → K → S) (inj : ∀ i, Function.Injective (x i))
    (seen : Finset S) :
    mean (fun k => ind (∃ i, x i k ∈ seen)) ≤ n * (seen.card / (Fintype.card K : ℝ)) := by
  classical
  have union (k : K) : ind (∃ i, x i k ∈ seen) ≤ ∑ i, ind (x i k ∈ seen) := by
    by_cases e : ∃ i, x i k ∈ seen
    · obtain ⟨i,hi⟩ := e
      exact (ind_le_one _).trans ((ind_pos hi) ▸ (Finset.single_le_sum
        (f := fun j => ind (x j k ∈ seen)) (fun _ _ => ind_nonneg _) (mem_univ i)))
    · simp [ind_neg e, Finset.sum_nonneg fun _ _ => ind_nonneg _]
  refine (avg_mono (A := univ) (fun k _ => union k)).trans ?_
  rw [avg_sum]
  exact (Finset.sum_le_sum fun i _ => key_hit (x i) (inj i) seen).trans_eq (by simp)

private theorem ind_or_le (P Q : Prop) : ind (P ∨ Q) ≤ ind P + ind Q := by
  by_cases hp : P
  · rw [ind_pos hp]
    linarith [ind_le_one (P ∨ Q), ind_nonneg Q]
  · by_cases hq : Q
    · rw [ind_pos hq]
      linarith [ind_le_one (P ∨ Q), ind_nonneg P]
    · rw [ind_neg (fun h => h.elim hp hq), ind_neg hp, ind_neg hq]
      norm_num

theorem bad_expectation (x : Fin n → K → S) (xi : ∀ i, Function.Injective (x i))
    (encode : Fin n → K → S) (ei : ∀ i, Function.Injective (encode i))
    (g : Strat S Bool) {q : Nat} (bound : g.QB q) :
    mean (fun k : K => mean (fun h : Fin n → K => g.exp PState.init (fun _ st =>
      ind (LinkedBad x k (fun i => encode i (h i)) st.trace)))) ≤
      n * ((3*q+2*n : ℝ)/Fintype.card K) := by
  classical
  simp_rw [exp_mean]
  rw [← g.exp_const (n * ((3*q+2*n : ℝ)/Fintype.card K)) PState.init Trace.WF.nil]
  apply Strat.exp_le_exp_of_post (Strat.post_and (g.post_inv _ Trace.WF.nil) (Strat.post_QB bound _))
  intro b st post
  have len : st.trace.length ≤ q := by simpa [PState.init] using post.2.1
  have ci : st.trace.usedIn.card = st.trace.length := post.1.1.card_usedIn
  have co : st.trace.usedOut.card = st.trace.length := post.1.1.card_usedOut
  have pos : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have first (h : Fin n → K) :
      mean (fun k => ind (∃ i, x i k ∈ st.trace.usedIn ∪ univ.image (fun i => encode i (h i)))) ≤
        n * (((q : ℝ) + n) / Fintype.card K) := by
    refine (input_hits x xi _).trans ?_
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply div_le_div_of_nonneg_right _ pos.le
    have c1 := Finset.card_union_le st.trace.usedIn (univ.image (fun i => encode i (h i)))
    have c2 : (univ.image (fun i => encode i (h i))).card ≤ n :=
      Finset.card_image_le.trans (by rw [Finset.card_univ, Fintype.card_fin])
    have c3 : (st.trace.usedIn ∪ univ.image (fun i => encode i (h i))).card ≤ q + n := by omega
    exact_mod_cast c3
  have second :
      mean (fun h : Fin n → K =>
        ind (Exposed (fun i => encode i (h i)) (st.trace.usedIn ∪ st.trace.usedOut))) ≤
        n * ((2 * (q : ℝ) + n) / Fintype.card K) := by
    have d := exposed_bound encode ei (st.trace.usedIn ∪ st.trace.usedOut)
    simp only [Fintype.card_fin] at d
    refine d.trans ?_
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply div_le_div_of_nonneg_right _ pos.le
    have c1 := Finset.card_union_le st.trace.usedIn st.trace.usedOut
    have c2 : (st.trace.usedIn ∪ st.trace.usedOut).card ≤ 2 * q := by omega
    have c3 : ((st.trace.usedIn ∪ st.trace.usedOut).card : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast c2
    linarith
  have split (k : K) (h : Fin n → K) :
      ind (LinkedBad x k (fun i => encode i (h i)) st.trace) ≤
        ind (∃ i, x i k ∈ st.trace.usedIn ∪ univ.image (fun i => encode i (h i))) +
        ind (Exposed (fun i => encode i (h i)) (st.trace.usedIn ∪ st.trace.usedOut)) :=
    ind_or_le _ _
  let A := fun (k : K) (h : Fin n → K) =>
    ind (∃ i, x i k ∈ st.trace.usedIn ∪ univ.image (fun i => encode i (h i)))
  let B := fun (h : Fin n → K) =>
    ind (Exposed (fun i => encode i (h i)) (st.trace.usedIn ∪ st.trace.usedOut))
  have sum_eq : mean (fun k => mean (fun h => A k h + B h)) =
      mean (fun h => mean (fun k => A k h)) + mean B := by
    have e1 : mean (fun k => mean (fun h => A k h + B h)) = mean (fun k => mean (A k) + mean B) :=
      avg_congr (fun k _ => avg_add)
    have e2 : mean (fun k => mean (A k) + mean B) =
        mean (fun k => mean (A k)) + mean (fun _ : K => mean B) := avg_add
    have e3 : mean (fun _ : K => mean B) = mean B := avg_const Finset.univ_nonempty _
    rw [e1, e2, e3, mean_swap A]
  calc mean (fun k => mean (fun h : Fin n → K => ind (LinkedBad x k (fun i => encode i (h i)) st.trace)))
      ≤ mean (fun k => mean (fun h => A k h + B h)) :=
        avg_mono fun k _ => avg_mono fun h _ => split k h
    _ = mean (fun h => mean (fun k => A k h)) + mean B := sum_eq
    _ ≤ n * (((q : ℝ) + n) / Fintype.card K) + n * ((2 * (q : ℝ) + n) / Fintype.card K) :=
        add_le_add (avg_le (by positivity) fun h _ => first h) second
    _ = n * ((3*q+2*n : ℝ)/Fintype.card K) := by ring

end CommitGolfCandidate.Permutation.LinkedSalt
