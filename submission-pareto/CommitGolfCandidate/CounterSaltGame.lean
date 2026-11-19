import CommitGolfCandidate.CounterSaltReplay
import CommitGolfCandidate.NonceChainGame

/-! A private key together with a public block counter selects distinct inputs.
The observer may know every extracted salt, including salts used after its first stage. -/
namespace CommitGolfCandidate.Permutation.CounterSalt
open Finset NonceChain
set_option linter.unusedSectionVars false
variable {S K D : Type} [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype K] [Nonempty K] [Fintype D] [Nonempty D] {n : Nat}

private theorem mean_swap {A B : Type} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    mean (fun a => mean (f a)) = mean (fun b => mean (fun a => f a b)) := by
  rw [← mean_prod, ← mean_prod]
  exact mean_equiv (Equiv.prodComm ..) (fun p : B × A => f p.2 p.1)

private theorem exp_mean {A T : Type} [Fintype A] (g : Strat S T) (s : PState S)
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

private theorem input_hits (x : Fin n → K → S) (inj : ∀ i, Function.Injective (x i)) (seen : Finset S) :
    mean (fun k => ind (∃ i, x i k ∈ seen)) ≤ n * (seen.card / (Fintype.card K : ℝ)) := by
  classical
  have union (k : K) : ind (∃ i, x i k ∈ seen) ≤ ∑ i, ind (x i k ∈ seen) := by
    by_cases e : ∃ i, x i k ∈ seen
    · obtain ⟨i,hi⟩ := e
      exact (ind_le_one _).trans ((ind_pos hi) ▸ (Finset.single_le_sum (f := fun j => ind (x j k ∈ seen))
        (fun _ _ => ind_nonneg _) (mem_univ i)))
    · simp [ind_neg e, Finset.sum_nonneg fun _ _ => ind_nonneg _]
  refine (avg_mono (A := univ) (fun k _ => union k)).trans ?_
  rw [avg_sum]
  exact (Finset.sum_le_sum fun i _ => key_hit (x i) (inj i) seen).trans_eq (by simp)

private theorem bad_expectation (g : Strat S Bool) {q : Nat} (bound : g.QB q)
    (x y : Fin n → K → S) (xi : ∀ i, Function.Injective (x i)) (yi : ∀ i, Function.Injective (y i)) :
    mean (fun k => mean (fun h : Fin n → K => g.exp PState.init (fun _ st =>
      ind (Bad (fun i => x i k) (fun i => y i (h i)) st.trace)))) ≤
       n * ((2*q+n : ℝ)/Fintype.card K) := by
  classical
  simp_rw [exp_mean]
  rw [← g.exp_const (n * ((2*q+n : ℝ)/Fintype.card K)) PState.init Trace.WF.nil]
  apply Strat.exp_le_exp_of_post (Strat.post_and (g.post_inv _ Trace.WF.nil) (Strat.post_QB bound _))
  intro b st post
  have len : st.trace.length ≤ q := by simpa [PState.init] using post.2.1
  let inp := fun k => ind (∃ i, x i k ∈ st.trace.usedIn)
  let out := fun (h : Fin n → K) => ind (Exposed (fun i => y i (h i)) st.trace.usedOut)
  have split (k : K) (h : Fin n → K) :
      ind (Bad (fun i => x i k) (fun i => y i (h i)) st.trace) ≤ inp k + out h := by
    unfold Bad inp out
    by_cases a : ∃ i, x i k ∈ st.trace.usedIn
    · rw [ind_pos a]
      linarith [ind_le_one ((∃ i, x i k ∈ st.trace.usedIn) ∨ Exposed (fun i => y i (h i)) st.trace.usedOut),
        ind_nonneg (Exposed (fun i => y i (h i)) st.trace.usedOut)]
    · simp only [a, false_or, ind_neg False.elim, zero_add, le_refl]
  have hi := input_hits x xi st.trace.usedIn
  have ho := exposed_bound y yi st.trace.usedOut
  have ci := post.1.1.card_usedIn
  have co := post.1.1.card_usedOut
  have l : (st.trace.length : ℝ) ≤ q := by exact_mod_cast len
  simp only [Fintype.card_fin,co,ci] at hi ho
  refine (avg_mono (A := univ) (fun k _ => avg_mono (A := univ) (fun h _ => split k h))).trans ?_
  simp only [avg_add, avg_const Finset.univ_nonempty]
  change mean inp + mean out ≤ _
  unfold inp out
  apply (add_le_add hi ho).trans
  rw [←mul_add,←add_div]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

private def partition : ((Fin n → D) × (Fin n → K)) ≃ (Fin n → D × K) where
  toFun z i := (z.1 i, z.2 i)
  invFun f := (fun i => (f i).1, fun i => (f i).2)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def realProb (split : S ≃ D × K) (x : Fin n → K → S)
    (g : (Fin n → D) → Strat S Bool) : ℝ :=
  mean fun π : Equiv.Perm S => mean fun k : K =>
    (g (fun i => (split (π (x i k))).1)).eager π PState.init (fun b _ => accept b)

private theorem sum_weight (split : S ≃ D × K) (x : Fin n → K → S) (g : (Fin n → D) → Strat S Bool) :
    (Fintype.card S : ℝ)^n * mean (fun p : Fin n → D => mean (fun k : K => mean (fun h : Fin n → K =>
      CounterSalt.weight (g p) (fun i => x i k) (fun i => split.symm (p i,h i))))) = CounterSalt.realProb split x g := by
  classical
  let F := fun (k : K) (z : Fin n → S) => CounterSalt.weight (g (fun i => (split (z i)).1)) (fun i => x i k) z
  have reorder (k : K) : mean (fun p : Fin n → D => mean (fun h : Fin n → K =>
      CounterSalt.weight (g p) (fun i => x i k) (fun i => split.symm (p i,h i)))) = mean (F k) := by
    let e := partition.trans (Equiv.piCongrRight fun _ : Fin n => split.symm)
    rw [← mean_prod, ← mean_equiv e (F k)]
    apply avg_congr
    rintro ⟨p,h⟩ _
    simp [e,F,partition]
    rfl
  rw [mean_swap (fun (p : Fin n → D) (k : K) => _)]
  simp_rw [reorder]
  unfold F CounterSalt.weight
  have followsEq (π : Equiv.Perm S) (k : K) (z : Fin n → S) :
      CounterSalt.follows π (fun i => x i k) z ↔ z = fun i => π (x i k) :=
    ⟨fun h => funext fun i => (h i).symm, fun e i => (congrFun e i).symm⟩
  simp_rw [followsEq]
  rw [← avg_mul_left]
  apply Eq.trans _ (mean_swap _)
  apply avg_congr
  intro k _
  rw [mean_swap, ← avg_mul_left]
  apply avg_congr
  intro π _
  unfold mean avg
  simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  rw [Finset.sum_ite_eq' univ]
  simp [field]

theorem ideal_le_counter (split : S ≃ D × K) (x : Fin n → K → S)
    (xi : ∀ i, Function.Injective (x i)) (distinct : ∀ k, Function.Injective fun i => x i k)
    (g : (Fin n → D) → Strat S Bool) (q : Nat) (bound : ∀ p, (g p).QB q) :
    NonceChain.idealProb g ≤ CounterSalt.realProb split x g + n * ((2*q+n : ℝ)/Fintype.card K) := by
  rw [← sum_weight]
  let err := n * ((2*q+n : ℝ)/Fintype.card K)
  change mean _ ≤ _ + err
  rw [← avg_mul_left, ← avg_const (Finset.univ_nonempty (α := Fin n → D)) err, ← avg_add]
  apply avg_mono
  intro p _
  let y := fun (i : Fin n) (h : K) => split.symm (p i,h)
  have step (k : K) (h : Fin n → K) := CounterSalt.path_comparison (g p) (fun i => x i k) (fun i => y i (h i)) (distinct k)
  have av := avg_mono (A := univ) (fun k _ => avg_mono (A := univ) (fun h _ => step k h))
  simp only [avg_const Finset.univ_nonempty, avg_add, avg_mul_left] at av
  exact av.trans (add_le_add_right (bad_expectation (g p) (bound p) x y xi
    (fun i a b eq => congrArg Prod.snd (split.symm.injective eq))) _)

end CommitGolfCandidate.Permutation.CounterSalt
