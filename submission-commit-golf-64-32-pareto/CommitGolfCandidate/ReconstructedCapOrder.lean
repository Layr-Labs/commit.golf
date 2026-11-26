import CommitGolfCandidate.ReconstructedHonestSizeSchedule
import CommitGolfCandidate.ReconstructedEncoding

namespace CommitGolfCandidate.Reconstruction.CapOrder
open HonestSizeSchedule HonestCapPlan

def window {A : Type} (f : Nat → A) (j : Nat) : Nat → List A
  | 0 => []
  | n+1 => f j :: window f (j+1) n

def entry (base : Nat) (f : Nat → Bool) (j : Nat) : List Nat :=
  if f (2*j) == f (2*j+1) then [] else [base+2*j+(f (2*j)).toNat]

def ids (base : Nat) (f : Nat → Bool) (j : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => entry base f j ++ ids base f (j+1) n

theorem window_length {A : Type} (f : Nat → A) (j n : Nat) : (window f j n).length=n := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih => simp only [window,List.length_cons,ih]

theorem window_get {A : Type} (f : Nat → A) (j n k : Nat) (inRange : k<n) :
    (window f j n)[k]'(by rw [window_length]; exact inRange)=f (j+k) := by
  induction n generalizing j k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => simp [window]
    | succ k =>
      simp only [window,List.getElem_cons_succ]
      exact (ih (j+1) k (by omega)).trans (congrArg f (by omega))

theorem window_list {A : Type} [Inhabited A] (xs : List A) :
    window (fun i => xs[i]?.getD default) 0 xs.length=xs := by
  apply List.ext_getElem
  · exact window_length _ _ _
  · intro i h hi
    rw [window_get _ _ _ _ hi,Nat.zero_add,List.getElem?_eq_getElem hi]
    rfl

theorem ids_snoc (base : Nat) (f : Nat → Bool) (j n : Nat) :
    ids base f j (n+1)=ids base f j n++entry base f (j+n) := by
  induction n generalizing j with
  | zero => simp [ids]
  | succ n ih =>
    change entry base f j ++ ids base f (j+1) (n+1) = (entry base f j ++ ids base f (j+1) n) ++ entry base f (j+(n+1))
    rw [ih (j+1),List.append_assoc,show j+1+n=j+(n+1) by omega]

theorem scan_window (base : Nat) (f : Nat → Bool) (j n : Nat) :
    Frontier.scan (base+2*j) (window f (2*j) (2*n)) =
      (window (fun k => f (2*k)||f (2*k+1)) j n,ids base f j n) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [show 2*(n+1)=(2*n+1)+1 by omega]
    simp only [window,Frontier.scan]
    have lo : 2*j+1+1=2*(j+1) := by omega
    have next : base+2*j+2=base+2*(j+1) := by omega
    rw [lo,next,ih]
    change (_,if f (2*j)==f (2*j+1) then ids base f (j+1) n else (base+2*j+(f (2*j)).toNat)::ids base f (j+1) n)=(_,entry base f j ++ ids base f (j+1) n)
    unfold entry
    split <;> rfl

theorem prefix_length (f : Nat → Bool) (depth n : Nat) :
    (ids (2^depth) (row f (9-depth)) 0 n).length=prefixCount f depth n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ids_snoc,List.length_append,ih,Nat.zero_add]
    change _+(entry (2^depth) (row f (9-depth)) n).length=_+(row f (9-depth) (2*n) != row f (9-depth) (2*n+1)).toNat
    unfold entry
    cases row f (9-depth) (2*n) <;> cases row f (9-depth) (2*n+1) <;> rfl

theorem id_bounds (base : Nat) (f : Nat → Bool) (j n k : Nat) (found : k∈ids base f j n) :
    base+2*j≤k ∧ k<base+2*(j+n) := by
  induction n generalizing j with
  | zero => cases found
  | succ n ih =>
    rcases List.mem_append.mp found with head|tail
    · unfold entry at head
      split at head
      · cases head
      · simp only [List.mem_singleton] at head
        have b : (f (2*j)).toNat≤1 := by cases f (2*j) <;> decide
        omega
    · have earlier := ih (j+1) tail
      omega

theorem id_cell (f : Nat → Bool) (d : Nat) (depth : 0<d) (high : d≤9) (j : Nat)
    (found : j∈ids (2^d) (row f (9-d)) 0 (pairs d)) : CommitParents.Cell d j := by
  have range := id_bounds _ _ _ _ _ found
  have width : 2*pairs d=2^d := by cases d with | zero => omega | succ d => simp [pairs,Nat.pow_succ]; omega
  change d≤24 ∧ 2^d≤j ∧ j<2^(d+1)
  simp only [Nat.mul_zero,Nat.add_zero,Nat.zero_add,width,Nat.pow_succ] at range ⊢
  omega

end CommitGolfCandidate.Reconstruction.CapOrder
