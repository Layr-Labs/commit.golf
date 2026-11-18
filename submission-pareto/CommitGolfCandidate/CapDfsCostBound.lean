import CommitGolfCandidate.CapDfsStep

/-! Conservative DFS resource ceilings derived from the exact macro costs.
The control bound permits at most 1022 macros. Opening has no cap queries and
each of its macros costs at most fifteen cycles. Connecting this sum to the
whole actual traversal and lower-record phase remains a separate theorem. -/
namespace CommitGolfCandidate
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

theorem cap_dfs_step_instruction_bound (checking : Bool) (marked : Nat → Bool)
    (control : CapDfsControl) :
    capDfsStepInstructions checking marked control ≤ 17 := by
  cases control <;> simp only [capDfsStepInstructions]
  all_goals try split_ifs
  all_goals omega

theorem cap_dfs_step_cycle_bound (checking : Bool) (marked : Nat → Bool)
    (control : CapDfsControl) :
    capDfsStepCycles checking marked control ≤ 19 := by
  cases control <;> simp only [capDfsStepCycles, capDfsStepInstructions]
  all_goals try split_ifs
  all_goals omega

theorem cap_dfs_step_open_cycle_bound (marked : Nat → Bool) (control : CapDfsControl) :
    capDfsStepCycles false marked control ≤ 15 := by
  cases control <;>
    simp only [capDfsStepCycles, capDfsStepInstructions, Bool.false_eq_true, ↓reduceIte]
  all_goals try split_ifs
  all_goals omega

theorem cap_dfs_step_query_bound (checking : Bool) (control : CapDfsControl) :
    capDfsStepQueries checking control ≤ 1 := by
  cases control <;> simp only [capDfsStepQueries]
  all_goals try split_ifs
  all_goals omega

theorem cap_dfs_step_open_queries (control : CapDfsControl) :
    capDfsStepQueries false control = 0 := by
  cases control <;> simp [capDfsStepQueries]

def capDfsCycleTotal (checking : Bool) (marked : Nat → Bool) :
    Nat → CapDfsControl → Nat
  | 0, _ => 0
  | fuel + 1, control =>
      capDfsStepCycles checking marked control +
        capDfsCycleTotal checking marked fuel (capControlStep marked control)

def capDfsInstructionTotal (checking : Bool) (marked : Nat → Bool) :
    Nat → CapDfsControl → Nat
  | 0, _ => 0
  | fuel + 1, control =>
      capDfsStepInstructions checking marked control +
        capDfsInstructionTotal checking marked fuel (capControlStep marked control)

def capDfsQueryTotal (checking : Bool) (marked : Nat → Bool) :
    Nat → CapDfsControl → Nat
  | 0, _ => 0
  | fuel + 1, control =>
      capDfsStepQueries checking control +
        capDfsQueryTotal checking marked fuel (capControlStep marked control)

theorem cap_dfs_cycle_total_bound (checking : Bool) (marked : Nat → Bool)
    (fuel : Nat) (control : CapDfsControl) :
    capDfsCycleTotal checking marked fuel control ≤ 19 * fuel := by
  induction fuel generalizing control with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      rw [capDfsCycleTotal]
      have first := cap_dfs_step_cycle_bound checking marked control
      have rest := ih (capControlStep marked control)
      omega

theorem cap_dfs_open_cycle_total_bound (marked : Nat → Bool)
    (fuel : Nat) (control : CapDfsControl) :
    capDfsCycleTotal false marked fuel control ≤ 15 * fuel := by
  induction fuel generalizing control with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      rw [capDfsCycleTotal]
      have first := cap_dfs_step_open_cycle_bound marked control
      have rest := ih (capControlStep marked control)
      omega

theorem cap_dfs_instruction_total_bound (checking : Bool) (marked : Nat → Bool)
    (fuel : Nat) (control : CapDfsControl) :
    capDfsInstructionTotal checking marked fuel control ≤ 17 * fuel := by
  induction fuel generalizing control with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      rw [capDfsInstructionTotal]
      have first := cap_dfs_step_instruction_bound checking marked control
      have rest := ih (capControlStep marked control)
      omega

theorem cap_dfs_query_total_bound (checking : Bool) (marked : Nat → Bool)
    (fuel : Nat) (control : CapDfsControl) :
    capDfsQueryTotal checking marked fuel control ≤ fuel := by
  induction fuel generalizing control with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
      rw [capDfsQueryTotal]
      have first := cap_dfs_step_query_bound checking control
      have rest := ih (capControlStep marked control)
      omega

/-- Includes the two real capWalk entry ADDIs as well as the separate setup,
record, mark and exit allowances. This arithmetic is not yet a full runtime
certificate for those phases. -/
theorem cap_coarse_opening_arithmetic :
    1022 * 15 + 128 * 266 + 2552 + 33 + 2 ≤ 60000 := by decide

end CommitGolfCandidate
