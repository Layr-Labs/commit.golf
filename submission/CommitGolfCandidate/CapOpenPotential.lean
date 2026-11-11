import CommitGolfCandidate.CapDfsCostBound
import CommitGolfCandidate.CapOpenPotentialData

/-! A weighted remaining-work potential bounds actual opening macro costs.
Unknown internal visits skip their subtree; returns cost at most five cycles. -/
namespace CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def capOpenPotential : CapDfsControl → Nat
  | .visit node => capOpenVisitPotential[node]?.getD 0
  | .advance node => capOpenAdvancePotential[node]?.getD 0
  | .done => 0

private theorem potential_table :
    ∀ node : Fin 256, 0<node.val →
      (15+capOpenPotential (.advance node.val) ≤ capOpenPotential (.visit node.val)) ∧
      (node.val<128 → 7+capOpenPotential (.visit (2*node.val)) ≤ capOpenPotential (.visit node.val)) ∧
      (1<node.val ∧ node.val%2=0 → 5+capOpenPotential (.visit (node.val+1)) ≤ capOpenPotential (.advance node.val)) ∧
      (1<node.val ∧ node.val%2=1 → 5+capOpenPotential (.advance (node.val/2)) ≤ capOpenPotential (.advance node.val)) := by
  decide

theorem cap_open_potential_step (marked : Nat → Bool) (control : CapDfsControl)
    (valid : CapDfsControlValid control) :
    capDfsStepCycles false marked control+capOpenPotential (capControlStep marked control) ≤
      capOpenPotential control := by
  cases control with
  | visit node =>
    obtain ⟨positive,bounded⟩ := valid
    have bounds := potential_table ⟨node,bounded⟩ positive
    dsimp only at bounds
    simp only [capDfsStepCycles,capDfsStepInstructions,capControlStep,Bool.false_eq_true,ite_false]
    by_cases selected : marked node=true
    · simp only [selected,Bool.true_and]
      by_cases internal : node<128
      · simpa [internal] using bounds.2.1 internal
      · simp [internal]
        omega
    · have unmarked : marked node=false := Bool.eq_false_iff.mpr selected
      simp only [unmarked,Bool.false_and,ite_false]
      exact bounds.1
  | advance node =>
    obtain ⟨positive,bounded⟩ := valid
    have bounds := potential_table ⟨node,bounded⟩ positive
    dsimp only at bounds
    simp only [capDfsStepCycles,capControlStep,Bool.false_eq_true,ite_false]
    by_cases root : node=1
    · subst node
      decide
    · simp only [if_neg root]
      by_cases even : node%2=0
      · simpa only [if_pos even] using bounds.2.2.1 ⟨by omega,even⟩
      · have odd : node%2=1 := by omega
        simpa only [if_neg even] using bounds.2.2.2 ⟨by omega,odd⟩
  | done => exact Nat.le_refl _

theorem cap_open_cycle_potential_bound (marked : Nat → Bool) (fuel : Nat)
    (control : CapDfsControl) (valid : CapDfsControlValid control) :
    capDfsCycleTotal false marked fuel control ≤ capOpenPotential control := by
  induction fuel generalizing control with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    rw [capDfsCycleTotal]
    have first := cap_open_potential_step marked control valid
    have rest := ih (capControlStep marked control) (cap_control_step_valid marked control valid)
    omega

theorem cap_open_cycle_4080 (marked : Nat → Bool) :
    capDfsCycleTotal false marked 510 (.visit 1) ≤ 4080 := by
  have bound := cap_open_cycle_potential_bound marked 510 (.visit 1) (by constructor <;> decide)
  have initial : capOpenPotential (.visit 1)=4080 := by decide
  simpa only [initial] using bound
end CommitGolfCandidate
