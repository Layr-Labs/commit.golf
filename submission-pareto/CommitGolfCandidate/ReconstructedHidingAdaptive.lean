import CommitGolfCandidate.ReconstructedHidingReplies
import CommitGolfCandidate.ReconstructedHidingView

namespace CommitGolfCandidate.Reconstruction.HidingTraffic
open CommitGolfCandidate.Permutation CommitGolfCandidate.Permutation.NonceChain Finset
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {S K : Type} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype K] [Nonempty K]

theorem avg_exchange {A B : Type} (left : Finset A) (right : Finset B) (f : A → B → ℝ) :
    avg left (fun a => avg right (f a)) = avg right (fun b => avg left (fun a => f a b)) := by
  unfold avg
  simp only [← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

def touches (ins outs : K → Finset S) (k : K) (x y : S) : Prop := x ∈ ins k ∨ y ∈ outs k
def containsPair (base : Trace S) (x y : S) : Prop := ∃ e ∈ base, e.inp=x ∧ e.out=y
def billable (base current : Trace S) (x y : S) : Prop :=
  containsPair base x y ∨ ¬containsPair current x y

private theorem indicator_union (a b : Prop) : ind (a ∨ b) ≤ ind a + ind b := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ind,ha,hb]

theorem fresh_payment (ins outs : K → Finset S) (x : S) (answers : Finset S)
    (u : Nat) (D δ : ℝ) (positive : 0 < D) (many : D ≤ answers.card)
    (direct : mean (fun k => ind (x ∈ ins k)) ≤ δ) (count : ∀ k, (outs k).card ≤ u) :
    mean (fun k => avg answers (fun y => ind (touches ins outs k x y))) ≤ δ + u/D := by
  have size (k : K) : avg answers (fun y => ind (y ∈ outs k)) ≤ u/D := by
    unfold avg
    have upper : ∑ y ∈ answers, ind (y ∈ outs k) ≤ (u:ℝ) := (sum_ind_le answers (outs k) (fun y => y ∈ outs k) (fun _ _ h => h)).trans
      (by exact_mod_cast count k)
    exact div_le_div₀ (Nat.cast_nonneg u) upper positive many
  have nonempty : answers.Nonempty := by
    rw [←Finset.card_pos]; exact_mod_cast (positive.trans_le many)
  have per (k : K) : avg answers (fun y => ind (touches ins outs k x y)) ≤ ind (x ∈ ins k) + u/D := by
    refine (avg_mono (fun y _ => indicator_union (x ∈ ins k) (y ∈ outs k))).trans ?_
    rw [avg_add,avg_const nonempty]
    exact add_le_add le_rfl (size k)
  exact (avg_mono (fun k _ => per k)).trans (by
    rw [avg_add,avg_const Finset.univ_nonempty]
    exact add_le_add direct le_rfl)

/-- A cached row that was selected before the public run may be requested
again. Its two endpoint guesses are charged together. All later repeats were
already paid for when the pair was first inserted. -/
theorem forward_payment (base current : Trace S)
    (ins outs : K → Finset S) (x : S) (u : Nat) (D δ : ℝ)
    (positive : 0 < D) (nonnegative : 0 ≤ δ) (many : D ≤ current.freeOut.card)
    (direct : mean (fun k => ind (x ∈ ins k)) ≤ δ) (count : ∀ k, (outs k).card ≤ u)
    (cached : ∀ y, containsPair base x y → mean (fun k => ind (touches ins outs k x y)) ≤ δ) :
    mean (fun k => avg (current.fwdAns x) (fun y =>
      ind (billable base current x y ∧ touches ins outs k x y))) ≤ δ + u/D := by
  by_cases seen : x ∈ current.usedIn
  · rw [mean,avg_exchange univ (current.fwdAns x) (fun k y => ind (billable base current x y ∧ touches ins outs k x y))]
    refine (avg_le nonnegative ?_).trans (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) positive.le))
    intro y answer
    rw [Trace.fwdAns,ite_eq_left seen,Trace.mem_fwdHits] at answer
    by_cases old : containsPair base x y
    · refine (avg_mono (fun k _ => ind_mono And.right)).trans (cached y old)
    · have marked : ¬billable base current x y := fun h => (h.resolve_left old) answer
      simp only [ind_neg (fun (h : billable base current x y ∧ _) => marked h.1),avg_zero,nonnegative]
  · rw [Trace.fwdAns,ite_eq_right seen]
    exact (avg_mono (fun k _ => avg_mono (fun y _ => ind_mono And.right))).trans
      (fresh_payment ins outs x current.freeOut u D δ positive many direct count)

theorem inverse_payment (base current : Trace S)
    (ins outs : K → Finset S) (y : S) (u : Nat) (D δ : ℝ)
    (positive : 0 < D) (nonnegative : 0 ≤ δ) (many : D ≤ current.freeIn.card)
    (direct : mean (fun k => ind (y ∈ outs k)) ≤ δ) (count : ∀ k, (ins k).card ≤ u)
    (cached : ∀ x, containsPair base x y → mean (fun k => ind (touches ins outs k x y)) ≤ δ) :
    mean (fun k => avg (current.invAns y) (fun x =>
      ind (billable base current x y ∧ touches ins outs k x y))) ≤ δ + u/D := by
  by_cases seen : y ∈ current.usedOut
  · rw [mean,avg_exchange univ (current.invAns y) (fun k x => ind (billable base current x y ∧ touches ins outs k x y))]
    refine (avg_le nonnegative ?_).trans (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg _) positive.le))
    intro x answer
    rw [Trace.invAns,ite_eq_left seen,Trace.mem_invHits] at answer
    obtain ⟨e,inTable,outEq,inEq⟩ := answer
    by_cases old : containsPair base x y
    · exact (avg_mono (fun k _ => ind_mono And.right)).trans (cached x old)
    · have marked : ¬billable base current x y := fun h => (h.resolve_left old) ⟨e,inTable,inEq,outEq⟩
      simp only [ind_neg (fun (h : billable base current x y ∧ _) => marked h.1),avg_zero,nonnegative]
  · rw [Trace.invAns,ite_eq_right seen]
    have flip (k : K) (x : S) : touches ins outs k x y → touches outs ins k y x := Or.symm
    exact (avg_mono (fun k _ => avg_mono (fun x _ => ind_mono (fun h => flip k x h.2)))).trans
      (fresh_payment outs ins y current.freeIn u D δ positive many direct count)

end CommitGolfCandidate.Reconstruction.HidingTraffic
