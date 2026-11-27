import CommitGolfCandidate.LateModel
import CommitGolfCandidate.Stage3cRow

namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolfCandidate.Late
open CommitGolf

def levelCount (height : Nat) := 2^(LOG_LENGTH-height)
def levelOffset (height : Nat) := 96*(LENGTH-levelCount height)
def nodeAddress (height i : Nat) := 4294975488 + levelOffset height + gapOffset i

theorem level_successor (height : Nat) (bound : height < LOG_LENGTH) :
    levelCount height = 2*levelCount (height+1) := by
  unfold levelCount
  rw [show LOG_LENGTH-height = (LOG_LENGTH-(height+1))+1 by omega, Nat.pow_succ, Nat.mul_comm]

theorem level_count_le (height : Nat) : levelCount height ≤ LENGTH := by
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  exact Nat.sub_le _ _

theorem level_adjacent (height : Nat) (bound : height < LOG_LENGTH) :
    levelOffset (height+1) = levelOffset height + 96*levelCount (height+1) := by
  have e := level_successor height bound
  have b := level_count_le height
  unfold levelOffset
  omega

theorem children_contiguous (height p : Nat) :
    nodeAddress height (2*p+1) = nodeAddress height (2*p)+32 ∧
    nodeAddress height (2*p) = 4294975488+levelOffset height+96*p := by
  unfold nodeAddress gapOffset
  omega

theorem parent_row_disjoint (height p j : Nat) (bound : height < LOG_LENGTH)
    (hp : p < levelCount (height+1)) :
    nodeAddress height (2*p)+96 ≤ nodeAddress (height+1) j := by
  rw [(children_contiguous height p).2]
  unfold nodeAddress
  rw [level_adjacent height bound]
  omega

theorem parent_below_salts (height j : Nat) (inside : j < levelCount height) :
    nodeAddress height j + 32 ≤ rowBase := by
  have n := level_count_le height
  unfold nodeAddress gapOffset levelOffset rowBase
  change levelCount height ≤ 16777216 at n
  change 4294975488 + 96*(16777216-levelCount height) + (96*(j/2)+32*(j%2)) + 32 ≤ 5905588224
  omega

end CommitGolfCandidate.Chained.BinaryMachine
