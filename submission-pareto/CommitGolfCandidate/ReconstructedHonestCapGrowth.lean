import CommitGolfCandidate.ReconstructedHonestCapPlan

namespace CommitGolfCandidate.Reconstruction.HonestCapGrowth
open HonestCapPlan

def levels : Nat → Nat
  | 0 => 0
  | d+1 => levels d+256*2^d+31*groups (2^d)

def remaining (v : Node) : Nat :=
  let d := v.depth
  let later := levels (d-1)
  let headers := fun n k => later+31*(groups n-k)
  let emit := fun n j => headers n 0+256*(n-j)
  match v.phase with
  | .enter => levels 9
  | .level | .scan .. | .scanGuard .. => emit (pairs d) 0
  | .collected n => emit n 0
  | .emit n j | .emitGuard n j => emit n j
  | .lowDone n => headers n 0
  | .group n k | .inner n k _ | .digitGuard n k _ | .flush n k | .groupGuard n k => headers n k
  | .finish => later
  | .returned => 0

def delta : Phase → Nat
  | .emit .. => 256
  | .flush .. => 31
  | _ => 0

private theorem atLevel (d : Nat) (pos : 0<d) : remaining ⟨d,.level⟩=levels d := by
  cases d with
  | zero => contradiction
  | succ d => simp [remaining,levels,pairs]; omega

theorem spent (v w : Node) (ok : legal v) (edge : w∈next v.depth v.phase) :
    delta v.phase+remaining w ≤ remaining v := by
  rcases v with ⟨d,p⟩
  cases p <;> simp only [next,List.mem_cons,List.not_mem_nil,or_false] at edge
  all_goals try contradiction
  all_goals try (rcases edge with rfl|rfl)
  all_goals try (obtain rfl := edge)
  all_goals simp only [legal,allowed,reduceCtorEq,ite_false] at ok
  all_goals try split
  all_goals try rw [atLevel (d-1) (by omega)]
  all_goals try rw [atLevel 9 (by decide)]
  all_goals simp only [remaining,delta,Nat.sub_zero,Nat.zero_add,groups]
  all_goals omega

theorem opening_max : 3633*128+remaining ⟨9,.enter⟩ ≤ 600000 := by decide

end CommitGolfCandidate.Reconstruction.HonestCapGrowth
