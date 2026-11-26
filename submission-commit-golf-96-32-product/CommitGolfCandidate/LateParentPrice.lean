import CommitGolfCandidate.LateParentSites

namespace CommitGolfCandidate.Late
open CommitGolf

/-- The measured parent program emits one setup per level, and a four-instruction
latch after each complete 32-parent block. The final five levels have no latch. -/
def parentCostAt (d : Nat) := parentBodyPC d-parentHeaderPC d +
  (7+siteWidth d)*levelCount (d+1) + 4*(levelCount (d+1)/32)

def parentStepsAt (d : Nat) := parentBodyPC d-parentHeaderPC d +
  siteWidth d*levelCount (d+1) + 4*(levelCount (d+1)/32)

theorem scheduled_cycles : 741933081 + 3 + ((List.range 24).map parentCostAt).sum + 11 = 915996948 := by decide

theorem scheduled_steps : 16842768 + 9 + (12*LENGTH + 2*(LENGTH/16) + 3*(LENGTH/32)) +
    3 + ((List.range 24).map parentStepsAt).sum + 11 = 278462747 := by decide

theorem scheduled_calls : 4*LENGTH + ((List.range 24).map fun d => levelCount (d+1)).sum = 83886079 := by decide

theorem contiguous_headers : ∀ d : Fin 23, parentEndPC d = parentHeaderPC (d.val+1) := by decide
theorem final_pc : parentEndPC 23 = 3785 := by decide

end CommitGolfCandidate.Late
