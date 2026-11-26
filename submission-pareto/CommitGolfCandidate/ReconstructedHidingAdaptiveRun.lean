import CommitGolfCandidate.ReconstructedHidingAdaptive

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolfCandidate.Permutation CommitGolfCandidate.Permutation.NonceChain Finset
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

variable {S K A : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype K] [Nonempty K]

noncomputable def tally (base : Trace S) (ins outs : K → Finset S) (k : K) :
    Strat S A → Trace S → ℝ
  | .done _, _ => 0
  | .rand _ next, t => avg univ fun i => tally base ins outs k (next i) t
  | .fwd x next, t => avg (t.fwdAns x) fun y =>
      ind (billable base t x y ∧ touches ins outs k x y) + tally base ins outs k (next y) (t.stepF x y)
  | .inv y next, t => avg (t.invAns y) fun x =>
      ind (billable base t x y ∧ touches ins outs k x y) + tally base ins outs k (next x) (t.stepI x y)

private theorem integrate_step {B : Type} (choices : Finset B) (pay cont : K → B → ℝ)
    (n : Nat) (rate : ℝ) (nonneg : 0 ≤ rate)
    (payment : mean (fun k => avg choices (pay k)) ≤ rate)
    (future : ∀ b ∈ choices, mean (fun k => cont k b) ≤ n*rate) :
    mean (fun k => avg choices (fun b => pay k b + cont k b)) ≤ ((n+1:Nat):ℝ)*rate := by
  simp_rw [avg_add]
  have later := avg_exchange univ choices cont
  refine (add_le_add payment (later.le.trans (avg_le (mul_nonneg (Nat.cast_nonneg _) nonneg) future))).trans_eq ?_
  push_cast
  ring

/-- The cumulative risk for both chosen and random endpoints of an adaptive
permutation strategy. 'cached' handles exposed pairs whose inputs and outputs
may be correlated. Subsequent repeat requests only use their first charge. -/
theorem tally_bound (base : Trace S) (ins outs : K → Finset S) (u Q : Nat) (δ : ℝ)
    (nonneg : 0 ≤ δ) (room : Q < Fintype.card S)
    (countIn : ∀ k, (ins k).card ≤ u) (countOut : ∀ k, (outs k).card ≤ u)
    (pickIn : ∀ x, mean (fun k => ind (x ∈ ins k)) ≤ δ)
    (pickOut : ∀ y, mean (fun k => ind (y ∈ outs k)) ≤ δ)
    (cached : ∀ x y, containsPair base x y → mean (fun k => ind (touches ins outs k x y)) ≤ δ)
    (g : Strat S A) (n : Nat) (bounded : g.QB n) (t : Trace S) (well : t.WF)
    (fit : t.length+n ≤ Q) :
    mean (fun k => tally base ins outs k g t) ≤ (n:ℝ)*(δ + u/((Fintype.card S:ℝ)-Q)) := by
  let D : ℝ := (Fintype.card S:ℝ)-Q
  have positive : 0 < D := sub_pos.mpr (by exact_mod_cast room)
  have rate : 0 ≤ δ+u/D := add_nonneg nonneg (div_nonneg (Nat.cast_nonneg _) positive.le)
  change _ ≤ (n:ℝ)*(δ+u/D)
  induction bounded generalizing t with
  | done a n =>
    rw [show mean (fun k => tally base ins outs k (.done a) t) = 0 from avg_zero]
    exact mul_nonneg (Nat.cast_nonneg _) rate
  | rand m next n _ ih =>
    change mean (fun k => avg univ (fun i => tally base ins outs k (next i) t)) ≤ _
    rw [mean,avg_exchange univ univ (fun k i => tally base ins outs k (next i) t)]
    exact avg_le (mul_nonneg (Nat.cast_nonneg _) rate) fun i _ => ih i t well fit
  | fwd x next n _ ih =>
    have many : D ≤ t.freeOut.card := by
      rw [well.card_freeOut,Nat.cast_sub well.length_le]
      have enough : (t.length:ℝ) ≤ Q := by exact_mod_cast (by omega : t.length ≤ Q)
      dsimp only [D]; linarith
    apply integrate_step (t.fwdAns x) _ _ n (δ+u/D) rate
    · exact forward_payment base t ins outs x u D δ positive nonneg many (pickIn x) countOut (cached x)
    · intro y allowed
      exact ih y (t.stepF x y) (well.stepF allowed) (by have := Trace.length_stepF_le t x y; omega)
  | inv y next n _ ih =>
    have many : D ≤ t.freeIn.card := by
      rw [well.card_freeIn,Nat.cast_sub well.length_le]
      have enough : (t.length:ℝ) ≤ Q := by exact_mod_cast (by omega : t.length ≤ Q)
      dsimp only [D]; linarith
    apply integrate_step (t.invAns y) _ _ n (δ+u/D) rate
    · exact inverse_payment base t ins outs y u D δ positive nonneg many (pickOut y) countIn (fun x => cached x y)
    · intro x allowed
      exact ih x (t.stepI x y) (well.stepI allowed) (by have := Trace.length_stepI_le t x y; omega)

end CommitGolfCandidate.Reconstruction.HidingTraffic
