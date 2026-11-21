import CommitGolfCandidate.ChainedQueryGraph

/-! Parameters and resource arithmetic for the chained internal layout. -/
namespace CommitGolfCandidate.Chained
open scoped BigOperators
set_option exponentiation.threshold 520

def calls (h : Height) : Nat :=
  if h.val < 8 then 4 else if h.val = 8 then 6 else if h.val < 15 then 8
  else if h.val = 15 then 4 else 1

def width (h : Height) : Nat :=
  if h.val < 8 then 234 else if h.val = 8 then 233 else if h.val < 15 then 232
  else if h.val = 15 then 234 else 238

theorem calls_positive : ∀ h, 0 < calls h := by decide +kernel
theorem calls_bound : ∀ h, calls h ≤ 8 := by decide +kernel
theorem width_lower : ∀ h, 232 ≤ width h := by decide +kernel
theorem width_upper : ∀ h, width h ≤ 238 := by decide +kernel
theorem density : ∀ h, 2^238 ≤ (calls h)^2*2^(width h) := by decide +kernel

theorem lower_work : (∑ h : Fin 16, calls ⟨h.val,by omega⟩) = 90 := by decide +kernel
theorem body_tail_bits : (∑ h : Fin 15, (width ⟨h.val,by omega⟩-232)) = 17 := by decide +kernel
theorem internal_commit_calls :
    (∑ h : Height, calls h*2^(23-h.val)) = 67302655 := by decide +kernel

def checkerBound (k : Nat) : Nat := 92*k+min (8*k) 255

theorem checker_budget (k : Nat) : checkerBound k ≤ 100*k := by
  unfold checkerBound
  have := Nat.min_le_left (8*k) 255
  omega

theorem checker_scored : checkerBound 128 = 12031 := rfl
theorem checker_singleton : checkerBound 1 = 100 := rfl
theorem checker_empty : checkerBound 0 = 0 := rfl
theorem full_replay : 2*checkerBound (2^24) = 3087008254 := rfl
theorem replay_room : 2*checkerBound (2^24) < 2^32 := by decide
theorem commit_calls : 67302655+2*2^24+1525248 = 102382335 := rfl
theorem commit_room : 102382335 ≤ 100*2^24 := by decide

end CommitGolfCandidate.Chained
