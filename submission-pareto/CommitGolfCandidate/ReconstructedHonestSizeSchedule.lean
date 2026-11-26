import CommitGolfCandidate.ReconstructedHonestCapPlan

namespace CommitGolfCandidate.Reconstruction.HonestSizeSchedule
open HonestCapPlan

/-- Number of true values in a prefix, with no assumptions about the function
outside the prefix. -/
def tally (f : Nat→Bool) : Nat→Nat
  | 0 => 0
  | n+1 => tally f n+(f n).toNat

def row (f : Nat→Bool) : Nat→Nat→Bool
  | 0,j => f j
  | h+1,j => row f h (2*j) || row f h (2*j+1)

def single (f : Nat→Bool) (h k : Nat) := row f h (2*k) != row f h (2*k+1)
def prefixCount (f : Nat→Bool) (d j : Nat) := tally (single f (9-d)) j
def missing (f : Nat→Bool) (d : Nat) := prefixCount f d (pairs d)
def population (f : Nat→Bool) (d : Nat) := tally (row f (9-d)) (2^d)

theorem tally_le (f : Nat→Bool) (n : Nat) : tally f n≤n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih => cases value : f n <;> simp [tally,value] <;> omega

theorem pair_count (f : Nat→Bool) (h n : Nat) :
    tally (row f h) (2*n)+tally (single f h) n=2*tally (row f (h+1)) n ∧
    tally (single f h) n≤tally (row f h) (2*n) ∧
    tally (row f (h+1)) n≤tally (row f h) (2*n) := by
  induction n with
  | zero => simp [tally]
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega]
    simp only [tally]
    rw [show row f (h+1) n=(row f h (2*n)||row f h (2*n+1)) from rfl,
      show single f h n=(row f h (2*n)!=row f h (2*n+1)) from rfl]
    cases a : row f h (2*n) <;> cases b : row f h (2*n+1) <;> simp <;> omega

theorem levels_count (f : Nat→Bool) (d : Nat) (lo : 0<d) (hi : d≤9) :
    population f d+missing f d=2*population f (d-1) ∧
    missing f d≤population f d ∧ population f (d-1)≤population f d := by
  have levels := pair_count f (9-d) (pairs d)
  have dep : 9-d+1=9-(d-1) := by omega
  have power : 2*pairs d=2^d := by cases d with | zero => contradiction | succ d => simp [pairs,Nat.pow_succ]; omega
  rw [power,dep] at levels
  exact levels

def ordinary (f : Nat→Bool) : Nat→Nat
  | 0 => 0
  | d+1 => ordinary f d+missing f (d+1)

theorem ordinary_bound (f : Nat→Bool) (d : Nat) (hi : d≤9) : ordinary f d+population f d≤2^d := by
  induction d with
  | zero => simpa only [ordinary,Nat.zero_add,population] using tally_le (row f (9-0)) (2^0)
  | succ d ih =>
    have prev := ih (by omega)
    have ⟨relation,_,_⟩ := levels_count f (d+1) (by omega) hi
    simp only [Nat.add_sub_cancel] at relation
    have old : population f d≤2^d := tally_le _ _
    simp only [ordinary,Nat.pow_succ]
    omega

def width (d : Nat) := if d<8 then 240 else 224
def headerBits (d n : Nat) := if d<8 then 0 else 31*groups n
def total (f : Nat→Bool) : Nat→Nat
  | 0 => 0
  | d+1 => total f d+width (d+1)*missing f (d+1)+headerBits (d+1) (missing f (d+1))

private theorem lower (f : Nat→Bool) (d : Nat) (hi : d<8) : total f d=240*ordinary f d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [total,ih (by omega)]
    simp only [width,headerBits,ite_eq_left hi,ordinary,Nat.mul_add,Nat.add_zero]

/-- The nine lengths from a heap with at most 128 occupied leaf flags,
including both separately rounded header groups. -/
theorem cap_bound (f : Nat→Bool) (few : population f 9≤128) : total f 9≤59328 := by
  have depth9 := levels_count f 9 (by decide) (by decide)
  have depth8 := levels_count f 8 (by decide) (by decide)
  have ordinary7 := ordinary_bound f 7 (by decide)
  change population f 9+missing f 9=2*population f 8 ∧ _ ∧ population f 8≤population f 9 at depth9
  change population f 8+missing f 8=2*population f 7 ∧ _ ∧ population f 7≤population f 8 at depth8
  change ordinary f 7+population f 7≤128 at ordinary7
  rw [show total f 9=total f 7+224*missing f 8+31*groups (missing f 8)+224*missing f 9+31*groups (missing f 9)
    from rfl,lower f 7 (by decide)]
  have upper9 := Nat.le_trans depth9.2.1 few
  have upper8 := Nat.le_trans depth8.2.1 (Nat.le_trans depth9.2.2 few)
  have combined : missing f 8+missing f 9≤2*population f 7 := by omega
  unfold groups
  clear depth9 depth8 few
  omega

def rightCount (f : Nat→Bool) (d : Nat) : Phase→Prop
  | .scan j p | .scanGuard j p => p=prefixCount f d j
  | .collected n | .emit n _ | .emitGuard n _ | .lowDone n | .group n _ | .inner n _ _
  | .digitGuard n _ _ | .flush n _ | .groupGuard n _ => n=missing f d
  | _ => True

def future (f : Nat→Bool) (v : Node) : Nat :=
  let d := v.depth
  let n := missing f d
  let below := total f (d-1)
  let headers := fun k => if d<8 then 0 else 31*(groups n-k)
  let emit := fun j => below+headers 0+width d*(n-j)
  match v.phase with
  | .enter => total f 9
  | .level | .scan .. | .scanGuard .. | .collected .. => emit 0
  | .emit _ j | .emitGuard _ j => emit j
  | .lowDone _ => below+headers 0
  | .group _ j | .inner _ j _ | .digitGuard _ j _ | .flush _ j | .groupGuard _ j => below+headers j
  | .finish => below
  | .returned => 0

def paid (d : Nat) : Phase→Nat
  | .emit .. => width d
  | .flush .. => 31
  | _ => 0

private theorem level_total (f : Nat→Bool) (d : Nat) (pos : 0<d) : future f ⟨d,.level⟩=total f d := by
  cases d with
  | zero => contradiction
  | succ d =>
    simp only [future,total,Nat.add_sub_cancel,Nat.sub_zero,width,headerBits]
    split <;> omega

theorem advance (f : Nat→Bool) (v w : Node) (ok : legal v) (counts : rightCount f v.depth v.phase)
    (edge : w∈next v.depth v.phase) : paid v.depth v.phase+future f w=future f v := by
  obtain ⟨d,p⟩ := v
  cases p <;> simp only [next,List.mem_cons,List.not_mem_nil,or_false] at edge
  all_goals try contradiction
  all_goals try (rcases edge with rfl|rfl)
  all_goals try (obtain rfl := edge)
  all_goals simp only [rightCount] at counts
  all_goals try (obtain rfl := counts)
  all_goals simp only [legal,allowed,reduceCtorEq,ite_false] at ok
  all_goals try split
  all_goals try rw [level_total f (d-1) (by omega)]
  all_goals try rw [level_total f 9 (by decide)]
  all_goals simp only [paid,future,Nat.sub_zero,Nat.zero_add,width,groups]
  all_goals repeat' split
  all_goals try (rw [show d-1=0 by omega]; rfl)
  all_goals omega

end CommitGolfCandidate.Reconstruction.HonestSizeSchedule
