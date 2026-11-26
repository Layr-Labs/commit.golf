import Std

namespace CommitGolfCandidate.Reconstruction.HonestCapPlan

inductive Phase where
  | enter | level | scan (j p : Nat) | scanGuard (k p : Nat) | collected (n : Nat)
  | emit (n j : Nat) | emitGuard (n k : Nat) | lowDone (n : Nat)
  | group (n j : Nat) | inner (n j remaining : Nat) | digitGuard (n j remaining : Nat)
  | flush (n j : Nat) | groupGuard (n k : Nat) | finish | returned
  deriving DecidableEq, Repr

structure Node where
  depth : Nat
  phase : Phase
  deriving DecidableEq, Repr

def pairs (d : Nat) := 2^(d-1)
def groups (n : Nat) := (n+3)/4

def pc : Phase → Nat
  | .enter => 1429 | .level => 1451 | .scan .. => 1470 | .scanGuard .. => 1469
  | .collected .. => 1483 | .emit .. => 1512 | .emitGuard .. => 1511 | .lowDone .. => 1581
  | .group .. => 1603 | .inner .. => 1610 | .digitGuard .. => 1625 | .flush .. => 1626
  | .groupGuard .. => 1602 | .finish => 1449 | .returned => 1641

def fee : Phase → Nat
  | .enter => 19 | .level => 14 | .scan .. => 17 | .scanGuard .. => 1
  | .collected .. => 26 | .emit .. => 59 | .emitGuard .. => 1 | .lowDone .. => 16
  | .group .. => 7 | .inner .. => 18 | .digitGuard .. => 1 | .flush .. => 19
  | .groupGuard .. => 1 | .finish => 2 | .returned => 0

def allowed (d : Nat) : Phase → Prop
  | .enter => d = 9
  | .level | .finish | .returned => True
  | .scan j p => j < pairs d ∧ p ≤ j
  | .scanGuard k p => 0 < k ∧ k ≤ pairs d ∧ p ≤ k
  | .collected n => n ≤ pairs d
  | .emit n j => n ≤ pairs d ∧ j < n
  | .emitGuard n k => n ≤ pairs d ∧ 0 < k ∧ k ≤ n
  | .lowDone n => n ≤ pairs d ∧ 0 < n
  | .group n j | .flush n j => 8 ≤ d ∧ n ≤ pairs d ∧ 4*j < n
  | .inner n j r => 8 ≤ d ∧ n ≤ pairs d ∧ 4*j < n ∧ 0 < r ∧ r ≤ 4
  | .digitGuard n j r => 8 ≤ d ∧ n ≤ pairs d ∧ 4*j < n ∧ r < 4
  | .groupGuard n k => 8 ≤ d ∧ n ≤ pairs d ∧ 0 < k ∧ 4*(k-1) < n

def legal (v : Node) := (if v.phase = .returned then v.depth = 0 else 0 < v.depth ∧ v.depth ≤ 9) ∧ allowed v.depth v.phase

def next (d : Nat) : Phase → List Node
  | .enter => [⟨9,.level⟩]
  | .level => [⟨d,.scan 0 0⟩]
  | .scan j p => [⟨d,.scanGuard (j+1) p⟩,⟨d,.scanGuard (j+1) (p+1)⟩]
  | .scanGuard k p => [⟨d,if k < pairs d then .scan k p else .collected p⟩]
  | .collected n => [⟨d,if n=0 then .finish else .emit n 0⟩]
  | .emit n j => [⟨d,.emitGuard n (j+1)⟩]
  | .emitGuard n k => [⟨d,if k=n then .lowDone n else .emit n k⟩]
  | .lowDone n => [⟨d,if d<8 then .finish else .group n 0⟩]
  | .group n j => [⟨d,.inner n j (min 4 (n-4*j))⟩]
  | .inner n j r => [⟨d,.digitGuard n j (r-1)⟩]
  | .digitGuard n j r => [⟨d,if r=0 then .flush n j else .inner n j r⟩]
  | .flush n j => [⟨d,.groupGuard n (j+1)⟩]
  | .groupGuard n k => [⟨d,if 4*k<n then .group n k else .finish⟩]
  | .finish => [if d=1 then ⟨0,.returned⟩ else ⟨d-1,.level⟩]
  | .returned => []

/-- A natural-number certificate for termination and worst-case cap work. A
112-cycle allowance covers all four digit visits of a cap header plus its setup
and flush. -/
def levels : Nat → Nat
  | 0 => 0
  | d+1 => levels d + 58 + 78*2^d + 112*groups (2^d)

def potential (v : Node) : Nat :=
  let d := v.depth
  let endCost := levels (d-1)+2
  let groupCost := fun n j => endCost + 112*(groups n-j)
  let low := fun n => 16+groupCost n 0
  let collected := fun n => 26+low n + 60*n
  let scan := fun j => collected (pairs d)+18*(pairs d-j)
  let flush := fun n j => 20+groupCost n (j+1)
  match v.phase with
  | .enter => 19+levels 9
  | .level => 14+scan 0
  | .scan j _ => scan j
  | .scanGuard k _ => 1+scan k
  | .collected n => collected n
  | .emit n j => low n+60*(n-j)
  | .emitGuard n k => 1+low n+60*(n-k)
  | .lowDone n => low n
  | .group n j => groupCost n j
  | .inner n j r => flush n j+19*r
  | .digitGuard n j r => 1+flush n j+19*r
  | .flush n j => flush n j
  | .groupGuard n k => 1+groupCost n k
  | .finish => endCost
  | .returned => 0

private theorem level_eq (d : Nat) (pos : 0 < d) : potential ⟨d,.level⟩ = levels d := by
  cases d with
  | zero => contradiction
  | succ d => simp [potential,levels,pairs]; omega

theorem entry_cost : potential ⟨9,.enter⟩ = 54847 := by decide

theorem width_bound (d : Nat) (hi : d ≤ 9) : pairs d ≤ 256 :=
  Nat.pow_le_pow_right (by decide) (show d-1 ≤ 8 by omega)

/-- Every transition modelled by the actual cutpoints preserves bounds, and
pays at least its machine segment price from a strictly decreasing potential. -/
theorem decreases (v w : Node) (legalV : legal v) (edge : w ∈ next v.depth v.phase) :
    legal w ∧ fee v.phase + potential w ≤ potential v ∧ potential w < potential v := by
  rcases v with ⟨d,phase⟩
  have posPairs : 0 < pairs d := Nat.two_pow_pos _
  cases phase <;> simp only [next,List.mem_cons,List.not_mem_nil,or_false] at edge
  all_goals try contradiction
  all_goals try (rcases edge with rfl|rfl)
  all_goals try (obtain rfl := edge)
  all_goals simp only [legal,allowed,reduceCtorEq,ite_false] at legalV
  all_goals try split
  all_goals try rw [level_eq (d-1) (by omega)]
  all_goals try rw [level_eq 9 (by decide)]
  all_goals simp only [legal,allowed,reduceCtorEq,ite_false,ite_true,fee,potential,Nat.sub_zero,groups,
    Nat.mul_zero,Nat.add_zero,Nat.zero_le,Nat.zero_lt_succ,true_and,and_true]
  all_goals omega

end CommitGolfCandidate.Reconstruction.HonestCapPlan
