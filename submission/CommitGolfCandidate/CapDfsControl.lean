import CommitGolfCandidate.CapDfsRank

namespace CommitGolfCandidate

inductive CapDfsControl where
  | visit (node : Nat)
  | advance (node : Nat)
  | done
  deriving DecidableEq

def CapDfsControlValid : CapDfsControl → Prop
  | .visit node | .advance node => 0 < node ∧ node < 512
  | .done => True

def capControlRank : CapDfsControl → Nat
  | .visit node => capVisitRank node
  | .advance node => capAdvanceRank node
  | .done => 1022

def capControlStep (marked : Nat → Bool) : CapDfsControl → CapDfsControl
  | .visit node =>
      if marked node && decide (node < 256) then .visit (2 * node) else .advance node
  | .advance node =>
      if node = 1 then .done
      else if node % 2 = 0 then .visit (node + 1) else .advance (node / 2)
  | .done => .done

theorem cap_control_step_valid (marked : Nat → Bool) (control : CapDfsControl)
    (valid : CapDfsControlValid control) :
    CapDfsControlValid (capControlStep marked control) := by
  cases control with
  | visit node =>
      obtain ⟨positive, bounded⟩ := valid
      simp only [capControlStep]
      split
      · rename_i selected
        simp only [Bool.and_eq_true, decide_eq_true_eq] at selected
        have internal : node < 256 := selected.2
        change 0 < 2 * node ∧ 2 * node < 512
        omega
      · exact ⟨positive, bounded⟩
  | advance node =>
      obtain ⟨positive, bounded⟩ := valid
      simp only [capControlStep]
      split
      · trivial
      · rename_i nonroot
        split
        · rename_i even
          change 0 < node + 1 ∧ node + 1 < 512
          omega
        · change 0 < node / 2 ∧ node / 2 < 512
          omega
  | done => trivial

theorem cap_control_rank_bounded (control : CapDfsControl)
    (valid : CapDfsControlValid control) : capControlRank control ≤ 1022 := by
  cases control with
  | visit node =>
      obtain ⟨positive, bounded⟩ := valid
      have before := cap_visit_terminal_rank node positive bounded
      have last := cap_advance_rank_bounded node positive bounded
      change capVisitRank node ≤ 1022
      omega
  | advance node =>
      exact Nat.le_of_lt (cap_advance_rank_bounded node valid.1 valid.2)
  | done => exact Nat.le_refl _

theorem cap_control_rank_before_done (control : CapDfsControl)
    (valid : CapDfsControlValid control) (unfinished : control ≠ .done) :
    capControlRank control < 1022 := by
  cases control with
  | visit node =>
      exact Nat.lt_trans (cap_visit_terminal_rank node valid.1 valid.2)
        (cap_advance_rank_bounded node valid.1 valid.2)
  | advance node => exact cap_advance_rank_bounded node valid.1 valid.2
  | done => exact False.elim (unfinished rfl)

theorem cap_control_step_progress (marked : Nat → Bool) (control : CapDfsControl)
    (valid : CapDfsControlValid control) (unfinished : control ≠ .done) :
    capControlRank control < capControlRank (capControlStep marked control) := by
  cases control with
  | visit node =>
      obtain ⟨positive, bounded⟩ := valid
      simp only [capControlStep]
      split
      · rename_i selected
        simp only [Bool.and_eq_true, decide_eq_true_eq] at selected
        have internal : node < 256 := selected.2
        change capVisitRank node < capVisitRank (2 * node)
        rw [cap_descend_rank node positive internal]
        omega
      · exact cap_visit_terminal_rank node positive bounded
  | advance node =>
      obtain ⟨positive, bounded⟩ := valid
      simp only [capControlStep]
      split
      · rename_i root
        subst node
        change capAdvanceRank 1 < 1022
        have finished := cap_root_done_rank
        omega
      · rename_i nonroot
        have higher : 1 < node := by omega
        split
        · rename_i even
          change capAdvanceRank node < capVisitRank (node + 1)
          rw [cap_sibling_rank node higher bounded even]
          omega
        · rename_i odd
          have parity : node % 2 = 1 := by omega
          change capAdvanceRank node < capAdvanceRank (node / 2)
          rw [cap_ascent_rank node higher bounded parity]
          omega
  | done => exact False.elim (unfinished rfl)

def capControlRun (marked : Nat → Bool) : Nat → CapDfsControl → CapDfsControl
  | 0, control => control
  | fuel + 1, control => capControlRun marked fuel (capControlStep marked control)

theorem cap_control_run_done (marked : Nat → Bool) (fuel : Nat)
    (control : CapDfsControl) (valid : CapDfsControlValid control)
    (budget : 1022 ≤ capControlRank control + fuel) :
    capControlRun marked fuel control = .done := by
  induction fuel generalizing control with
  | zero =>
      by_cases finished : control = .done
      · exact finished
      · have before := cap_control_rank_before_done control valid finished
        simp only [Nat.add_zero] at budget
        omega
  | succ fuel ih =>
      rw [capControlRun]
      by_cases finished : control = .done
      · subst control
        exact ih .done trivial (by change 1022 ≤ 1022 + fuel; omega)
      · have nextValid := cap_control_step_valid marked control valid
        have progress := cap_control_step_progress marked control valid finished
        exact ih _ nextValid (by omega)

theorem cap_control_complete (marked : Nat → Bool) :
    capControlRun marked 1022 (.visit 1) = .done :=
  cap_control_run_done marked 1022 (.visit 1) (by constructor <;> decide) (by omega)

end CommitGolfCandidate
