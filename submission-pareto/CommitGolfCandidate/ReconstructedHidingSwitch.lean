import CommitGolfCandidate.ReconstructedHidingExposure

namespace CommitGolfCandidate.Reconstruction.HidingReplay
open CommitGolfCandidate.Permutation CommitGolfCandidate.Permutation.NonceChain Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable {S K D R : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype K] [Nonempty K] [Fintype D] [Nonempty D] [Fintype R] [Nonempty R] {n : Nat}

private theorem exchange {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y → ℝ) :
    mean (fun x => mean (f x)) = mean (fun y => mean (fun x => f x y)) := by
  rw [← mean_prod,← mean_prod]
  exact mean_equiv (Equiv.prodComm X Y) (fun p => f p.2 p.1)

private theorem exp_average {X B : Type} [Fintype X] (g : Strat S B)
    (s : PState S) (f : X → B → PState S → ℝ) :
    mean (fun x => g.exp s (f x)) = g.exp s (fun b st => mean (fun x => f x b st)) := by
  unfold mean avg
  simp_rw [div_eq_inv_mul, ← Strat.exp_sum, ← Strat.exp_mul_left]

private theorem mean_constant {X : Type} [Fintype X] [Nonempty X] (r : ℝ) :
    mean (fun _ : X => r) = r := avg_const Finset.univ_nonempty _

/-- After the public transcript, average over the still-independent secret key
and reserved output bits. A collision among visible parts is charged once. -/
theorem hidden_exposure (split : S ≃ D × R) (address : K → Fin n → S)
    (unique : ∀ k k' i j, address k i = address k' j → k = k' ∧ i = j)
    (d : Fin n → D) (t : Trace S) :
    mean (fun k : K => mean (fun r : Fin n → R =>
       ind (¬ Fresh (scheduled (address k) (fun i => split.symm (d i,r i))) t))) ≤
      ind (¬Function.Injective d) + t.usedIn.card/(Fintype.card K : ℝ) + t.usedOut.card/(Fintype.card R : ℝ) := by
  classical
  by_cases distinct : Function.Injective d
  · have input (k : K) : Function.Injective (address k) := fun i j eq => (unique _ _ _ _ eq).2
    have output (r : Fin n → R) : Function.Injective (fun i => split.symm (d i,r i)) := by
      intro i j eq
      exact distinct (congrArg Prod.fst (split.symm.injective eq))
    let badIn (k : K) := ∃ i, address k i ∈ t.usedIn
    let badOut (r : Fin n → R) := ∃ i, split.symm (d i,r i) ∈ t.usedOut
    have charge (k : K) (r : Fin n → R) :
        ind (¬Fresh (scheduled (address k) (fun i => split.symm (d i,r i))) t) ≤ ind (badIn k) + ind (badOut r) := by
      by_cases hi : badIn k
      · rw [ind_pos hi]; exact (ind_le_one _).trans (le_add_of_nonneg_right (ind_nonneg _))
      by_cases ho : badOut r
      · rw [ind_neg hi,ind_pos ho,zero_add]; exact ind_le_one _
      have fresh := scheduled_fresh (address k) (fun i => split.symm (d i,r i)) t
        (input k) (output r) (fun i h => hi ⟨i,h⟩) (fun i h => ho ⟨i,h⟩)
      rw [scheduled,ind_neg (not_not_intro fresh),ind_neg hi,ind_neg ho,add_zero]
    have left := used_input_bound address (fun k k' i j eq => (unique k k' i j eq).1) t.usedIn
    have right := used_output_bound split d distinct t.usedOut
    rw [ind_neg (not_not_intro distinct),zero_add]
    refine (avg_mono (fun k _ => avg_mono (fun r _ => charge k r))).trans ?_
    simp_rw [avg_add,avg_const Finset.univ_nonempty]
    exact add_le_add left right
  · have upper : mean (fun k : K => mean (fun r : Fin n → R =>
        ind (¬ Fresh (scheduled (address k) (fun i => split.symm (d i,r i))) t))) ≤ 1 :=
      avg_le (by positivity) (fun _ _ => avg_le (by positivity) (fun _ _ => ind_le_one _))
    rw [ind_pos distinct]
    exact upper.trans (by linarith [show 0 ≤ (t.usedIn.card:ℝ)/Fintype.card K by positivity, show 0 ≤ (t.usedOut.card:ℝ)/Fintype.card R by positivity])

theorem keyed_switch (split : S ≃ D × R) (address : K → Fin n → S)
    (unique : ∀ k k' i j, address k i = address k' j → k = k' ∧ i = j)
    (g : (Fin n → D) → Strat S Bool) (q : Nat) (bounded : ∀ d, (g d).QB q) :
    idealRun g ≤ realRun split address g +
      ((q:ℝ)/Fintype.card K + q/Fintype.card R + (n:ℝ)*n/Fintype.card D) := by
  classical
  refine (compare_runs split address g).trans (add_le_add (le_refl _) ?_)
  have rewriteBlocks (d : Fin n → D) (r : Fin n → R) :
      publicBlocks split (fun i => split.symm (d i,r i)) = d :=
    funext fun i => congrArg Prod.fst (split.apply_symm_apply (d i, r i))
  simp_rw [split_average split (fun y => (g (publicBlocks split y)).exp PState.init _),rewriteBlocks]
  rw [exchange]
  simp_rw [exp_average]
  have run (d : Fin n → D) :
      (g d).exp PState.init (fun _ st => mean (fun k : K => mean (fun r : Fin n → R =>
        ind (¬Fresh (scheduled (address k) (fun i => split.symm (d i,r i))) st.trace)))) ≤
        ind (¬Function.Injective d) + (q:ℝ)/Fintype.card K + q/Fintype.card R := by
    rw [← (g d).exp_const (ind (¬Function.Injective d) + (q:ℝ)/Fintype.card K + q/Fintype.card R) PState.init Trace.WF.nil]
    apply Strat.exp_le_exp_of_post (Strat.post_and ((g d).post_inv _ Trace.WF.nil)
      (Strat.post_QB (bounded d) PState.init))
    intro b st facts
    have len : st.trace.length ≤ q := by simpa [PState.init] using facts.2.1
    have li : st.trace.usedIn.card ≤ q := facts.1.1.card_usedIn.trans_le len
    have lo : st.trace.usedOut.card ≤ q := facts.1.1.card_usedOut.trans_le len
    refine (hidden_exposure split address unique d st.trace).trans ?_
    gcongr
  refine (avg_mono (fun d _ => run d)).trans ?_
  simp_rw [avg_add, avg_const Finset.univ_nonempty]
  linarith [duplicate_parts_bound (n := n) (D := D)]

end CommitGolfCandidate.Reconstruction.HidingReplay
