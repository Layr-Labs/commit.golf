import CommitGolfCandidate.CapDfsCostBound
import CommitGolfCandidate.BoundaryPotentialData
import CommitGolfCandidate.CapDfsBoundaryOrder

namespace CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def capBoundaryPotential : CapDfsControl → Nat
  | .visit node => capBoundaryVisitPotential[node]?.getD 0
  | .advance node => capBoundaryAdvancePotential[node]?.getD 0
  | .done => 0

private theorem potential_table :
    ∀ node : Fin 512, 0<node.val →
      (15+capBoundaryPotential (.advance node.val) ≤ capBoundaryPotential (.visit node.val)+10) ∧
      (5+capBoundaryPotential (.advance node.val) ≤ capBoundaryPotential (.visit node.val)) ∧
      (node.val<256 → 7+capBoundaryPotential (.visit (2*node.val)) ≤ capBoundaryPotential (.visit node.val)) ∧
      (1<node.val ∧ node.val%2=0 → 5+capBoundaryPotential (.visit (node.val+1)) ≤ capBoundaryPotential (.advance node.val)) ∧
      (1<node.val ∧ node.val%2=1 → 5+capBoundaryPotential (.advance (node.val/2)) ≤ capBoundaryPotential (.advance node.val)) := by
  decide

theorem cap_boundary_potential_step (marked : Nat → Bool) (control : CapDfsControl)
    (valid : CapDfsControlValid control) :
    capDfsStepCycles false marked control+capBoundaryPotential (capControlStep marked control) ≤
      capBoundaryPotential control + 10*(capControlBoundaryHead marked control).length := by
  cases control with
  | visit node =>
    obtain ⟨positive,bounded⟩ := valid
    have bounds := potential_table ⟨node,bounded⟩ positive
    dsimp only at bounds
    simp only [capDfsStepCycles,capDfsStepInstructions,capControlStep,capControlBoundaryHead,Bool.false_eq_true,ite_false]
    by_cases selected : marked node=true
    · simp only [selected,Bool.true_and,ite_true,List.length_nil,Nat.mul_zero,Nat.add_zero]
      by_cases internal : node<256
      · simpa [internal] using bounds.2.2.1 internal
      · simpa [internal] using bounds.2.1
    · have unmarked : marked node=false := Bool.eq_false_iff.mpr selected
      simp only [unmarked,Bool.false_and,ite_false,List.length_singleton,Nat.mul_one]
      exact bounds.1
  | advance node =>
    obtain ⟨positive,bounded⟩ := valid
    have bounds := potential_table ⟨node,bounded⟩ positive
    dsimp only at bounds
    simp only [capDfsStepCycles,capControlStep,capControlBoundaryHead,List.length_nil,Nat.mul_zero,Nat.add_zero,Bool.false_eq_true,ite_false]
    by_cases root : node=1
    · subst node
      decide
    · simp only [if_neg root]
      by_cases even : node%2=0
      · simpa only [if_pos even] using bounds.2.2.2.1 ⟨by omega,even⟩
      · have odd : node%2=1 := by omega
        simpa only [if_neg even] using bounds.2.2.2.2 ⟨by omega,odd⟩
  | done => exact Nat.le_refl _

theorem cap_boundary_cycle_potential_bound (marked : Nat → Bool) (fuel : Nat)
    (control : CapDfsControl) (valid : CapDfsControlValid control) :
    capDfsCycleTotal false marked fuel control ≤ capBoundaryPotential control +
      10*(capControlBoundaries marked fuel control).length := by
  induction fuel generalizing control with
  | zero => exact Nat.zero_le _
  | succ fuel ih =>
    rw [capDfsCycleTotal,capControlBoundaries,List.length_append]
    have first := cap_boundary_potential_step marked control valid
    have rest := ih (capControlStep marked control) (cap_control_step_valid marked control valid)
    omega

theorem cap_boundary_cycle_bound (marked : Nat → Bool) :
    capDfsCycleTotal false marked 1022 (.visit 1) ≤
      5616 + 10*(capControlBoundaries marked 1022 (.visit 1)).length := by
  have bound := cap_boundary_cycle_potential_bound marked 1022 (.visit 1) (by constructor <;> decide)
  have initial : capBoundaryPotential (.visit 1)=5616 := by decide
  simpa only [initial] using bound
end CommitGolfCandidate
